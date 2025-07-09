/-
══════════════════════════════════════════════════════════════════════════════
     CantorUCI₂.lean   –   UCI-style diagonal argument for *enumerators*
══════════════════════════════════════════════════════════════════════════════

What this file proves
---------------------
*Let* `f : ℕ → ℕ → Bool` be a total, row-wise-computable map that purports
to enumerate all infinite bitstrings (reals in [0,1]):

  • **Total computable**:
      `Computable (fun p : ℕ × ℕ => f p.1 p.2)`

  • **Extensional on codes**: for any two codes whose *semantics* agree,
      every row of `f` agrees as well:

        c₁.eval = c₂.eval  ⇒  ∀ j, f ⌜c₁⌝ j = f ⌜c₂⌝ j

  • **Witness rows**: we are *given* two codes `badCode`, `goodCode`
      whose 0-th bits differ:

        f ⌜badCode⌝ 0 = 0 ,   f ⌜goodCode⌝ 0 = 1

From these assumptions we derive `False` by instantiating the general
**`uciGeneral`** lemma with the classifier

    Φ i  :=  f i 0    -- first-column bit of row i

and the witnesses `badCode`, `goodCode`.

Relationship to the “classifier” proof (CantorUCI₁.lean)
---------------------------------------------------------
* **Same engine** – both proofs call `uciGeneral` *once* with `D = ℕ`.
* **Different front end**
  • *Classifier version* hard-codes the witnesses as the constant-0 and
    constant-1 programs; no user input needed.
  • *Enumerator version* treats a **binary** map `f` and therefore needs
    external evidence that its first column is non-constant.  Any truly
    surjective enumerator would supply such rows automatically; here we
    keep the statement minimal and leave that 1-line search lemma to the
    caller.

What it does **not** prove
--------------------------
* It does **not** build the witness codes itself; it merely consumes them.
  A separate lemma like

      find_first_column_witnesses :
        (∃ k, f k 0 = 0) → (∃ k, f k 0 = 1) →
        ∃ bad good, f bad 0 = 0 ∧ f good 0 = 1

  discharges that obligation for any non-trivial `f`.
* It does **not** switch the UCI domain from `ℕ` to `Code`; the latter
  would need an explicit `Numbering Code` instance, as explained in
  CantorUCI₁’s header.

Dependencies and guarantees
---------------------------
* Imports only Lean-core, mathlib4’s `PartrecCode`, and your
  `Godelnumbering` / `KleeneFix` modules – **no `Std4`** extras.
* Uses **no `sorry`** and no axioms beyond Lean’s classical logic.
* Compiles with

      lake build
      lean --run CantorUCI₂.lean

══════════════════════════════════════════════════════════════════════════════
-/
import Impossibility.UCICoreTest
import Mathlib.Computability.Primrec
import Mathlib.Data.Bool.Basic
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances
import Kleene2.KleeneFix


open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier

namespace CantorUCI

/-- classifier: first digit of row `i` in the putative enumeration `f` -/
noncomputable def bit (f : ℕ → ℕ → Bool) (i : ℕ) : Bool :=
  f i 0

/-- ① `bit` is computable if `f` is row-wise computable.               -/
lemma bit_comp {f : ℕ → ℕ → Bool}
    (hf_comp : Computable (fun p : ℕ × ℕ => f p.1 p.2)) :
    Computable (bit f) := by
  have pairComp : Computable (fun i : ℕ => (i, 0)) :=
    Computable.pair Computable.id (Computable.const 0)
  simpa [bit] using hf_comp.comp pairComp

/-- ② decoder on ℕ is the identity, hence computable.                  -/
lemma decode_comp :
  Computable (fun n : ℕ => (Numbering.decode n : ℕ)) :=
  by
    simpa using (Computable.id : Computable (fun n : ℕ => n))

/-- ③ extensionality transferred to the classifier `bit`.              -/
lemma bit_ext
    {f : ℕ → ℕ → Bool}
    (hf_ext :
      ∀ {c₁ c₂ : Code},
        c₁.eval = c₂.eval →
        ∀ j, f (Encodable.encode c₁) j = f (Encodable.encode c₂) j)
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    bit f (Numbering.decode (Encodable.encode c₁)) =
    bit f (Numbering.decode (Encodable.encode c₂)) := by
  have := hf_ext hEq 0
  simpa [bit, Numbering.decode_encode] using this

/-- Cantor–UCI contradiction.  Callers must supply *two* codes whose
    first-column bits differ; any non-trivial enumerator admits such a
    pair, mirroring the “good/bad” witnesses in HaltingUCI and RiceUCI. -/
theorem no_total_extensional_enumerator
    (f       : ℕ → ℕ → Bool)
    (hf_comp : Computable (fun p : ℕ × ℕ => f p.1 p.2))
    (hf_ext  :
      ∀ {c₁ c₂ : Code},
        c₁.eval = c₂.eval →
        ∀ j, f (Encodable.encode c₁) j = f (Encodable.encode c₂) j)
    (badCode goodCode : Code)                                 -- witnesses
    (hBad  : bit f (Numbering.decode (Encodable.encode badCode))  = false)
    (hGood : bit f (Numbering.decode (Encodable.encode goodCode)) = true) :
    False :=
by
  let Φ : Classifiers ℕ := ⟨bit f⟩
  exact
    Kleene.UCI.Classifier.uciGeneral (D := ℕ)
      Φ
      (bit_comp hf_comp)                -- ① classifier computable
      decode_comp                       -- ② decoder computable
      (bit_ext hf_ext)                  -- ③ extensionality
      badCode goodCode                  -- ④-⑤ witness codes
      (by                              -- classifier(bad)=false
        simpa using hBad)
      (by                              -- classifier(good)=true
        simpa using hGood)

end CantorUCI
