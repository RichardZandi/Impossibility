/-
TimeLineUCI_param.lean
----------------------
Same content as the earlier “variable-based” file, but every lemma
takes its premises as explicit parameters.
Just import this file and instantiate the final
`no_total_timeline_decider` with your concrete data.
-/

import Impossibility.UCICoreTest
import Mathlib.Computability.PartrecCode
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances

open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier

namespace TimeLineUCI

/-- Bundle an arbitrary Boolean predicate as a classifier. -/
noncomputable def Φ (T : ℕ → Bool) : Classifiers ℕ := ⟨T⟩

lemma Φ_comp
    {T : ℕ → Bool}
    (hT_comp : Computable T) :
    Computable (Φ T).C :=
  hT_comp

/-- Lift code-extensionality into the shape required by `uciGeneral`. -/
lemma Φ_ext
    {T : ℕ → Bool}
    (hT_ext :
      ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
        T (Encodable.encode c₁) = T (Encodable.encode c₂))
    {c₁ c₂ : Code}
    (hEq : c₁.eval = c₂.eval) :
    (Φ T).C (Numbering.decode (Encodable.encode c₁)) =
    (Φ T).C (Numbering.decode (Encodable.encode c₂)) := by
  simpa [Φ] using hT_ext (c₁ := c₁) (c₂ := c₂) hEq


lemma timeline_contradiction
    {T : ℕ → Bool}
    (hT_comp  : Computable T)
    (hT_ext   :
      ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
        T (Encodable.encode c₁) = T (Encodable.encode c₂))
    {iFalse iTrue : ℕ}
    (hFalse : T iFalse = false)
    (hTrue  : T iTrue  = true) :
    False := by
  -- witnesses need to be *codes*, so wrap them with `numToCode`
  have bit_false : (Φ T).C (numToCode iFalse) = false := by
    simpa [Φ, Numbering.decode_encode] using hFalse
  have bit_true  : (Φ T).C (numToCode iTrue)  = true  := by
    simpa [Φ, Numbering.decode_encode] using hTrue

  -- run the diagonal engine
  exact
    Kleene.UCI.Classifier.uciGeneral (D := ℕ)
      (Φ T)
      (Φ_comp hT_comp)
      (by
        simpa using (Computable.id : Computable (fun n : ℕ => n)))
      (Φ_ext hT_ext)
      (numToCode iFalse) (numToCode iTrue)
      bit_false
      bit_true

theorem no_total_timeline_decider :
  ¬ ∃ (T : ℕ → Bool),
       Computable T ∧
       (∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
          T (Encodable.encode c₁) = T (Encodable.encode c₂)) ∧
       (∃ iF, T iF = false) ∧
       (∃ iT, T iT = true) := by
  rintro ⟨T, hComp, hExt, ⟨iF, hF⟩, ⟨iT, hT⟩⟩
  exact
    timeline_contradiction hComp hExt hF hT

end TimeLineUCI
