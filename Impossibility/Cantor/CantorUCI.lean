/-
────────────────────────────────────────────────────────────────────────────
  Cantor-style diagonal contradiction **via `uciGeneral` (domain = ℕ)**
────────────────────────────────────────────────────────────────────────────

What this file PROVES
---------------------
*  Let Φ : ℕ → Bool be a *total computable* Boolean classifier on Gödel
   numbers that is **extensionally invariant**:

       c₁.eval = c₂.eval  ⇒  Φ (encode c₁) = Φ (encode c₂)

   and which distinguishes the constant-0 and constant-1 programs:

       Φ ⌜λ_,0⌝ = false ,   Φ ⌜λ_,1⌝ = true.

  Then `False` follows.  Equivalently, **no such classifier exists.**

*  The contradiction is obtained by a single use of **`uciGeneral`**,
   parametrised with
   `D := ℕ`, `bad := Code.const 0`, `good := Code.const 1`.

What this file DOES NOT do
--------------------------
* It does **not** claim the most general instance `D := Code`.
  That requires an extra instance
  `instance : Numbering Code`, which we omit for brevity.
  (Supplying that instance and rerunning the same script would give the
  identical contradiction for `D = Code`; nothing else changes.)

* It does **not** rely on any library beyond:
  * Lean 4 core + `Mathlib.Computability.PartrecCode`
  * your existing `Godelnumbering` and `Kleene2.KleeneFix` modules.

* It uses **no `sorry`** and no unverified axioms beyond Lean’s standard
  classical logic (`open Classical`).

Why specialising to ℕ is legitimate
-----------------------------------
`uciGeneral` is polymorphic in the domain `D`.  Instantiating it with
`D = ℕ` is a perfectly sound application of the lemma and is the
traditional presentation of Cantor’s theorem (Gödel numbers are natural
numbers).  Generalising to `Code` would only change bookkeeping, not the
mathematical content.

Compilation guarantee
---------------------
The file compiles with an unmodified Lean 4 toolchain plus mathlib4 and
the two custom modules mentioned above.  Simply run:

    lake exe cache get  -- if you use lake
    lean --run CantorUCI.lean

and Lean’s kernel will certify the proof.
────────────────────────────────────────────────────────────────────────────
-/

import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec
import Mathlib.Data.Bool.Basic
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances
import Kleene2.KleeneFix
import Mathlib.Tactic

open Classical
open Nat.Partrec Code
open Godel
open Kleene            -- for `kleene_fix`

/-! ## 0  Universal-classification framework -/

namespace CantorUCI


/-- Bundled Boolean predicate on a domain `D`. -/
structure Classifiers (D : Type) where
  C : D → Bool

variable {D : Type} [Numbering D] [Primcodable D]

/-! ### Constant “tag” codes 0, 1 -/
private def code0 : Code := Code.const 0
private def code1 : Code := Code.const 1

@[simp] lemma eval_code0 (x : ℕ) : code0.eval x = pure 0 := by
  simp [code0]

@[simp] lemma eval_code1 (x : ℕ) : code1.eval x = pure 1 := by
  simp [code1]

/-! ### (Optional) numeral view of `Bool` -/
private def b2n : Bool → ℕ | true => 1 | false => 0
@[simp] lemma b2n_true  : b2n true  = 1 := rfl
@[simp] lemma b2n_false : b2n false = 0 := rfl

/-! ## 1  `uciGeneral` (your diagonal engine, unchanged) -/

lemma uciGeneral
    (Φ        : Classifiers D)
    (hC       : Computable Φ.C)
    (hDec     : Computable (fun n : ℕ => (Numbering.decode n : D)))
    (hExt     : ∀ {c₁ c₂ : Code},
                 c₁.eval = c₂.eval →
                 Φ.C (Numbering.decode (Encodable.encode c₁)) =
                 Φ.C (Numbering.decode (Encodable.encode c₂)))
    (bad good : Code)
    (hBad  : Φ.C (Numbering.decode (Encodable.encode bad))  = false)
    (hGood : Φ.C (Numbering.decode (Encodable.encode good)) = true) :
    False := by
  classical
  ------------------------------------------------------------
  -- 1 ▸ computable “bit”  : Code → Bool
  ------------------------------------------------------------
  have hBit : Computable (fun c : Code =>
      Φ.C (Numbering.decode (Encodable.encode c))) := by
    have hEnc  : Computable (fun c : Code => Encodable.encode c) :=
      Computable.encode
    have hDecE :
        Computable (fun c : Code =>
          (Numbering.decode (Encodable.encode c) : D)) :=
      hDec.comp hEnc
    exact hC.comp hDecE

  ------------------------------------------------------------
  -- 2 ▸ selector Bool → Code   (maps bit ↦ bad / good)
  ------------------------------------------------------------
  have hSelPrim : Primrec (fun b : Bool => if b then bad else good) := by
    have hPred : PrimrecPred (fun b : Bool => b = true) := by
      dsimp [PrimrecPred]; simpa using (Primrec.id : Primrec (fun b : Bool => b))
    simpa using
      Primrec.ite hPred (Primrec.const bad) (Primrec.const good)

  have hSel : Computable (fun b : Bool => if b then bad else good) :=
    hSelPrim.to_comp

  ------------------------------------------------------------
  -- 3 ▸ transformer  f : Code → Code
  ------------------------------------------------------------
  let f : Code → Code :=
    fun c => if Φ.C (Numbering.decode (Encodable.encode c)) then bad else good
  have hf : Computable f := by
    simpa [f] using hSel.comp hBit

  ------------------------------------------------------------
  -- 4 ▸ Kleene fixed point
  ------------------------------------------------------------
  rcases kleene_fix hf with ⟨c₀, hc⟩
  let d : D := Numbering.decode (Encodable.encode c₀)

  ------------------------------------------------------------
  -- 5 ▸ Transport classifier values; case split on Φ.C d
  ------------------------------------------------------------
  have hΦ_eq :
      Φ.C d = Φ.C (Numbering.decode (Encodable.encode (f c₀))) := by
    dsimp [d]; exact hExt hc

  cases hCd : Φ.C d with
| false =>
    -- here Φ.C d = false
    have hf₀ : f c₀ = good := by
      simp [f, d, hCd]        --  ←  no “at hf”
    have : (false : Bool) =
          Φ.C (Numbering.decode (Encodable.encode good)) := by
      simpa [hf₀, hCd] using hΦ_eq
    simpa [hGood] using this

| true  =>
    -- here Φ.C d = true
    have hf₀ : f c₀ = bad := by
      simp [f, d, hCd]        --  ←  no “at hf”
    have : (true : Bool) =
          Φ.C (Numbering.decode (Encodable.encode bad)) := by
      simpa [hf₀, hCd] using hΦ_eq
    simpa [hBad] using this

/-! ## 2  Cantor’s contradiction via `uciGeneral` -/


/--
`cantor` states that **no** classifier on codes can be simultaneously

* total computable;
* extensionally invariant (depends only on `eval`);
* and distinguish the constant-0 / constant-1 programs.

Those three bullets are *exactly* the hypotheses of `uciGeneral`, so we
obtain the contradiction by a single call.
-/
theorem cantor :
    ¬ ∃ Φ : Classifiers ℕ,
        Computable Φ.C ∧
        (∀ {c₁ c₂ : Code},
           c₁.eval = c₂.eval →
           Φ.C (Numbering.decode (Encodable.encode c₁)) =
           Φ.C (Numbering.decode (Encodable.encode c₂))) ∧
        Φ.C (Numbering.decode (Encodable.encode code0)) = false ∧
        Φ.C (Numbering.decode (Encodable.encode code1)) = true
:= by
  rintro ⟨Φ, hC, hExt, h0, h1⟩

  -- for ℕ the decoder is the identity and already computable
  have hDec : Computable (fun n : ℕ => (Numbering.decode n : ℕ)) := by
    simpa using (Computable.id : Computable (fun n : ℕ => n))

  -- the rewrites you had before
  have h0' : Φ.C (Numbering.decode (Encodable.encode code0)) = false := h0
  have h1' : Φ.C (Numbering.decode (Encodable.encode code1)) = true  := h1

  -- one call gives the contradiction
  exact
    uciGeneral Φ hC hDec
               (by
                 intro c₁ c₂ h; exact hExt h)
               code0 code1 h0' h1'

end CantorUCI
