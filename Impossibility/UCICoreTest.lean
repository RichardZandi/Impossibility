/-
────────────────────────────────────────────────────────────────────────
  Kleene.UCI.Classifier  –  universal–classification impossibility
────────────────────────────────────────────────────────────────────────

### Concept recap
* `Code`                   ― Gödel numbers for partial recursive programs.
* `Numbering.decode n : D` ― a *transport* that re-interprets the natural
  number `n` as a value of the target domain `D`.  (Usually `D = ℕ`,
  but the machinery is completely polymorphic.)
* `Classifiers D`          ― a *bundled* Boolean predicate `C : D → Bool`.
  We keep the computability proof separate from the data to avoid passing
  it around by hand.

### File contents
1.  **Helper codes `code0`, `code1`**
    Tiny programs returning the numerals 0 and 1.  They act as *Boolean tags*
    for the general UCI engine.  Nothing prevents callers from supplying
    their own “bad / good” witnesses, but the hard-wired pair is convenient
    for the classic use-case.

2.  **`uciGeneral` (main theorem)**
    ```
    Φ computable
    Φ respects extensionality
    Φ(bad)  = false
    Φ(good) = true
    ───────────────────────────────
                   ⊥
    ```
    *Proof idea*   Diagonalise: build a code transformer
    ```
      f c := if Φ (decode ⌜c⌝) then bad else good
    ```
    obtain its Kleene fixed point `c₀`, evaluate both sides at 0, and
    observe that Φ must assign *both* truth-values to `bad` (or `good`),
    which is impossible.

3.  **Wrapper lemma `uci`**
    Maintains the original API expected by existing proofs: it simply calls
    `uciGeneral` with `bad = Code.const 0`, `good = Code.const 1`.

### Key implementation notes
* **Computable plumbing** `hBit` and `hSel` show that both the bit extractor
  and the selector are computable; therefore `f` is computable and we may
  apply Rogers/Kleene fixed-point theorem (`kleene_fix hf`).
* **Extensionality bridge** `hΦ_eq` ports the classifier value across the
  semantic equality `c₀.eval = (f c₀).eval`.
* **Boolean case split** Finally we split on the bit `Φ.C d` and obtain
  the contradiction with `hBad`, `hGood`.

No `sorry` — the proof is fully constructive and standalone.
-/

import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec
import Mathlib.Data.Bool.Basic
import Kleene2.KleeneFix            -- kleene_fix
import Godelnumbering.Transport

open Classical
open Godel
open Nat.Partrec Code
open Primrec
open Kleene       -- for `kleene_fix`


namespace Kleene.UCI
namespace Classifier

/-! ## Classifier bundle -/

/-! A *bundled* Boolean predicate on `D`.  Bundling keeps the classifier’s
    computability proof (`hC`) separate from its definition. -/
/-- Bundled Boolean predicate on a domain `D`. -/
structure Classifiers (D : Type) where
  /-- The underlying Boolean predicate. -/
  C : D → Bool

variable {D : Type} [Numbering D] [Primcodable D]

/-! ## Constant codes used as Boolean tags  -/

private def code0 : Code := Code.const 0   -- ⟨∅⟩
private def code1 : Code := Code.const 1   -- ⟨true⟩

@[simp] lemma eval_code0 (x : ℕ) : code0.eval x = pure 0 := by
  simp [code0]

@[simp] lemma eval_code1 (x : ℕ) : code1.eval x = pure 1 := by
  simp [code1]

/-! ## Numeral helper for `Bool` (may be useful elsewhere) -/
private def b2n : Bool → ℕ | true => 1 | false => 0
@[simp] lemma b2n_true  : b2n true  = 1 := rfl
@[simp] lemma b2n_false : b2n false = 0 := rfl

/-! ## Universal Classification Impossibility  -/


/-! -----------------------------------------------------------------
    ##  General engine
------------------------------------------------------------------- -/

/-- **`uciGeneral` – Universal-classification impossibility
    with caller-supplied witnesses.**

If a bundled classifier `Φ` is

* total computable (`hC`);
* respects code‐level extensionality (`hExt`);
* and maps `bad ↦ false`, `good ↦ true`;

then `False` follows.

The proof is the standard Kleene–diagonal construction:
build a transformer `f`, get its Kleene fixed point `c₀`, then show
`Φ` contradicts itself on that fixed point. -/

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
  -- 1 ▸ computable “bit” : Code → Bool
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
      have hf₀ : f c₀ = good := by simp [f, d, hCd]
      have : (false : Bool) =
          Φ.C (Numbering.decode (Encodable.encode good)) := by
        simpa [hf₀, hCd] using hΦ_eq
      simpa [hGood] using this

  | true  =>
      have hf₀ : f c₀ = bad := by simp [f, d, hCd]
      have : (true : Bool) =
          Φ.C (Numbering.decode (Encodable.encode bad)) := by
        simpa [hf₀, hCd] using hΦ_eq
      simpa [hBad] using this

/-! -----------------------------------------------------------------
    ##  Wrapper (original API)
------------------------------------------------------------------- -/


/-- Compatibility wrapper that hard-codes
    `bad = Code.const 0`, `good = Code.const 1`. -/
lemma uci
    (Φ    : Classifiers D)
    (hC   : Computable Φ.C)
    (hDec : Computable (fun n : ℕ => (Numbering.decode n : D)))
    (hExt : ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
            Φ.C (Numbering.decode (Encodable.encode c₁)) =
            Φ.C (Numbering.decode (Encodable.encode c₂)))
    (h0 : Φ.C (Numbering.decode (Encodable.encode code0)) = false)
    (h1 : Φ.C (Numbering.decode (Encodable.encode code1)) = true) :
    False := uciGeneral Φ hC hDec hExt code0 code1 h0 h1


end Classifier
end Kleene.UCI


#lint
