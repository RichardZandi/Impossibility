/-
CreatorParadoxUCI_param.lean
----------------------------
Creator-paradox proof with explicit parameters (no `variable` blocks).
The witnesses are genuine `Code`s, matching `uciGeneral`’s signature.
-/

import Impossibility.UCICoreTest
import Mathlib.Computability.PartrecCode
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances

open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier

namespace CreatorParadoxUCI

/-- Bundle a Boolean predicate as a classifier. -/
abbrev Φ (Judge : ℕ → Bool) : Classifiers ℕ := ⟨Judge⟩

/-- Computability of the wrapper. -/
lemma Φ_comp {Judge : ℕ → Bool}
    (hComp : Computable Judge) :
    Computable (Φ Judge).C :=
  hComp

/-- Lift extensionality into the exact shape `uciGeneral` needs. -/
lemma Φ_ext
    {Judge : ℕ → Bool}
    (hExt :
      ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
        Judge (Encodable.encode c₁) =
        Judge (Encodable.encode c₂))
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    (Φ Judge).C (Numbering.decode (Encodable.encode c₁)) =
    (Φ Judge).C (Numbering.decode (Encodable.encode c₂)) := by
  simpa [Φ, Numbering.decode_encode] using hExt hEq

/-- **Core contradiction**: any total, extensional, non-trivial
    `Judge` collapses under the UCI diagonal.  `Produce` is passed only
    for completeness; the proof itself never touches it. -/
theorem creator_contradiction
    (Produce : ℕ → Code)                    -- blueprint enumerator (unused)
    (Judge   : ℕ → Bool)                   -- creator’s verdict
    (hComp   : Computable Judge)           -- total computable
    (hExt    :
      ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
        Judge (Encodable.encode c₁) =
        Judge (Encodable.encode c₂))       -- extensional
    (cBad  cGood : Code)                   -- witness codes
    (hBad  : Judge (Encodable.encode cBad)  = false)
    (hGood : Judge (Encodable.encode cGood) = true) :
    False := by
  ------------------------------------------------------------------
  -- “Bit” lemmas in the form `uciGeneral` expects
  ------------------------------------------------------------------
  have bit_bad :
      (Φ Judge).C (Numbering.decode (Encodable.encode cBad)) = false := by
    simpa [Φ, Numbering.decode_encode] using hBad
  have bit_good :
      (Φ Judge).C (Numbering.decode (Encodable.encode cGood)) = true := by
    simpa [Φ, Numbering.decode_encode] using hGood

  ------------------------------------------------------------------
  -- Apply the generic diagonal engine
  ------------------------------------------------------------------
  exact
    Kleene.UCI.Classifier.uciGeneral (D := ℕ)
      (Φ Judge)                 -- classifier on ℕ
      (Φ_comp hComp)            -- computability
      (by                        -- decoder ℕ → ℕ is just `id`
        simpa using
          (Computable.id : Computable (fun n : ℕ => n)))
      (Φ_ext hExt)              -- extensionality
      cBad cGood                -- witness codes
      bit_bad bit_good          -- their classifier values

/-- **Headline theorem**: no such creator can exist. -/
theorem no_total_creator_decider :
  ¬ ∃ (Produce : ℕ → Code) (Judge : ℕ → Bool),
        Computable Judge ∧
        (∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
           Judge (Encodable.encode c₁) = Judge (Encodable.encode c₂)) ∧
        (∃ cB : Code,  Judge (Encodable.encode cB)  = false) ∧
        (∃ cG : Code,  Judge (Encodable.encode cG) = true) := by
  rintro ⟨Produce, Judge, hComp, hExt, ⟨cB, hB⟩, ⟨cG, hG⟩⟩
  exact creator_contradiction
          Produce Judge hComp hExt
          cB cG hB hG

end CreatorParadoxUCI
