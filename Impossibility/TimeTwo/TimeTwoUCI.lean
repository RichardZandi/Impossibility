/-
TimeTwoUCI_param.lean
---------------------
Generic (parameter-based) UCI proof of the “Time-2” impossibility:

* D : ℕ → Bool               — candidate classifier
* D is computable and respects extensionality of `Code.eval`
* D is non-trivial (there are codes with D-bit = false / true)

From these we derive `False`.  The last theorem packages the
contradiction in the usual ∃-free form.
-/

import Impossibility.UCICoreTest
import Mathlib.Computability.PartrecCode
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances

open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier

namespace TimeTwoUCI

/-- Bundle a plain Boolean predicate into a `Classifiers` record. -/
abbrev Φ (D : ℕ → Bool) : Classifiers ℕ := ⟨D⟩

/-- If `D` is computable, so is the classifier’s component `C`. -/
lemma Φ_comp {D : ℕ → Bool} (hComp : Computable D) :
    Computable (Φ D).C := hComp

/-- Lift a Code-level extensionality proof into the shape `uciGeneral` needs. -/
lemma Φ_ext
    {D : ℕ → Bool}
    (hExt :
      ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
        D (Encodable.encode c₁) = D (Encodable.encode c₂))
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    (Φ D).C (Numbering.decode (Encodable.encode c₁)) =
    (Φ D).C (Numbering.decode (Encodable.encode c₂)) := by
  simpa [Φ, Numbering.decode_encode] using hExt hEq

/-- **Core contradiction**: a single concrete classifier `D` cannot be
    (i) total/ computable, (ii) extensional on `Code.eval`, and
    (iii) non-trivial (`bad`, `good` witnesses). -/
lemma timeTwo_contradiction
    (D              : ℕ → Bool)
    (hComp          : Computable D)
    (hExt           :
       ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
         D (Encodable.encode c₁) = D (Encodable.encode c₂))
    (bad good       : Code)          -- “false” / “true” witnesses
    (hBad  : D (Encodable.encode bad)  = false)
    (hGood : D (Encodable.encode good) = true) : False := by
  -- turn the two witness bits into the exact form expected by `uciGeneral`
  have bitBad  :
      (Φ D).C (Numbering.decode (Encodable.encode bad)) = false := by
    simpa [Φ, Numbering.decode_encode] using hBad
  have bitGood :
      (Φ D).C (Numbering.decode (Encodable.encode good)) = true := by
    simpa [Φ, Numbering.decode_encode] using hGood

  -- feed everything to the universal diagonal engine
  exact
    Kleene.UCI.Classifier.uciGeneral (D := ℕ)
      (Φ D)
      (Φ_comp hComp)
      (by
        simpa using (Computable.id : Computable (fun n : ℕ => n))) -- decoder ℕ→ℕ
      (Φ_ext hExt)
      bad good
      bitBad
      bitGood

/-- **Headline theorem (T₂)**:
    *⊥*: no computable, extensional, non-trivial total classifier exists. -/
theorem no_complete_internal_time_theory :
  ¬ ∃ (D : ℕ → Bool),
        Computable D ∧
        (∀ {c₁ c₂ : Code},
            c₁.eval = c₂.eval →
            D (Encodable.encode c₁) = D (Encodable.encode c₂)) ∧
        (∃ cBad : Code,  D (Encodable.encode cBad)  = false) ∧
        (∃ cGood : Code, D (Encodable.encode cGood) = true) := by
  rintro ⟨D, hComp, hExt, ⟨cB, hB⟩, ⟨cG, hG⟩⟩
  exact timeTwo_contradiction D hComp hExt cB cG hB hG

end TimeTwoUCI
