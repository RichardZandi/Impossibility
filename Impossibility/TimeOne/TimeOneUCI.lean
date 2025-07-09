/-
TimeLineUCI_param.lean
----------------------

UCI-style impossibility for a timeline “boundary” classifier, written so that
*every* assumption is an explicit parameter.

* `timeLine_contradiction`  – the conditional lemma (needs witnesses).
* `no_total_timeline_decider` – the project-complete headline theorem.
-/

import Impossibility.UCICoreTest
import Mathlib.Computability.PartrecCode
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances

open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier

namespace TimeLineUCI

/-- Pack any Boolean predicate on `ℕ` into a `Classifiers` record. -/
abbrev Φ (T : ℕ → Bool) : Classifiers ℕ := ⟨T⟩

/-- If `T` is computable, so is the classifier component `(Φ T).C`. -/
@[inline] def Φ_comp {T : ℕ → Bool} (hT_comp : Computable T) :
    Computable (Φ T).C := by
  -- `(Φ T).C = T` by definition, so this is just `hT_comp`
  simpa [Φ]

/-- Lift extensionality (`hT_ext`) into the exact shape `uciGeneral` needs. -/
@[inline] def Φ_ext
    {T : ℕ → Bool}
    (hT_ext :
      ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
        T (Encodable.encode c₁) = T (Encodable.encode c₂))
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    (Φ T).C (Numbering.decode (Encodable.encode c₁)) =
    (Φ T).C (Numbering.decode (Encodable.encode c₂)) := by
  -- `Numbering.decode (encode c) = c` for `ℕ`, then apply `hT_ext`
  simpa [Φ, Numbering.decode_encode] using hT_ext hEq

/-- Core contradiction: any total, computable, extensional,
    *non-trivial* predicate `T` collapses via UCI’s diagonal. -/
theorem timeLine_contradiction
    (T        : ℕ → Bool)
    (hT_comp  : Computable T)
    (hT_ext   : ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
                 T (Encodable.encode c₁) = T (Encodable.encode c₂))
    (cFalse cTrue : Code)
    (hFalse : T (Encodable.encode cFalse) = false)
    (hTrue  : T (Encodable.encode cTrue)  = true) : False := by
  ------------------------------------------------------------------
  -- Witness bits in the shape `uciGeneral` requires
  ------------------------------------------------------------------
  have bit_false :
      (Φ T).C (Numbering.decode (Encodable.encode cFalse)) = false := by
    simpa [Φ, Numbering.decode_encode] using hFalse
  have bit_true  :
      (Φ T).C (Numbering.decode (Encodable.encode cTrue)) = true := by
    simpa [Φ, Numbering.decode_encode] using hTrue

  ------------------------------------------------------------------
  -- Apply the generic diagonal engine
  ------------------------------------------------------------------
  exact
    Kleene.UCI.Classifier.uciGeneral (D := ℕ)
      (Φ T)                                 -- classifier
      (Φ_comp hT_comp)                      -- computability
      (by
        simpa using                         -- decoder ℕ → ℕ is `id`
          (Computable.id : Computable (fun n : ℕ => n)))
      (Φ_ext hT_ext)                        -- extensionality
      cFalse cTrue                          -- bad / good witnesses
      bit_false bit_true                    -- their bits

/-- **Headline theorem**:
    *No* total computable `T : ℕ → Bool` can
    (i) respect extensionality on `Code.eval` *and*
    (ii) be non-trivial (output both `false` and `true`). -/
theorem no_total_timeline_decider :
  ¬ ∃ (T : ℕ → Bool),
        Computable T ∧
        (∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
             T (Encodable.encode c₁) = T (Encodable.encode c₂)) ∧
        (∃ cF : Code, T (Encodable.encode cF) = false) ∧
        (∃ cT : Code, T (Encodable.encode cT) = true) := by
  ---------------------------------------------
  -- unpack the tuple the user SUPPOSES exists
  ---------------------------------------------
  rintro ⟨T, hComp, hExt, ⟨cF, hF⟩, ⟨cT, hT⟩⟩

  -- Now call the generic contradiction:
  have : False :=
    timeLine_contradiction T hComp hExt cF cT hF hT
  exact this


end TimeLineUCI
