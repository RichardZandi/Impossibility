/-
TimeLoopUCI_param.lean
----------------------
UCI proof of “no total, correct decider for causal self-loops”.

*  L : ℕ → Bool                — candidate classifier (“is the event in a loop?”)
*  hComp  : Computable L       — total/decidable
*  hExt   : extensionality     — same behaviour ⇒ same bit
*  cFalse , cTrue   : Code     — witnesses (one non-loop, one loop)
*  hFalse , hTrue             — their respective bits

Instantiating `no_total_loop_decider` with concrete ingredients
yields the final contradiction for your project.
-/

import Impossibility.UCICoreTest
import Mathlib.Computability.PartrecCode
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances

open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier

namespace TimeLoopUCI

/-- Wrap a Boolean predicate on `ℕ` into a `Classifiers` record. -/
abbrev Φ (L : ℕ → Bool) : Classifiers ℕ := ⟨L⟩

/-- If the predicate is computable, so is the classifier component. -/
lemma Φ_comp {L : ℕ → Bool} (hComp : Computable L) :
    Computable (Φ L).C := hComp

/-- Lift behavioural extensionality into the shape `uciGeneral` expects. -/
lemma Φ_ext
    {L : ℕ → Bool}
    (hExt :
      ∀ {c₁ c₂ : Code},                         -- extensionality on Codes
        c₁.eval = c₂.eval →
        L (Encodable.encode c₁) = L (Encodable.encode c₂))
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    (Φ L).C (Numbering.decode (Encodable.encode c₁)) =
    (Φ L).C (Numbering.decode (Encodable.encode c₂)) := by
  simpa [Φ, Numbering.decode_encode] using hExt hEq

/-- Core contradiction: a total, extensional, non-trivial loop-decider cannot exist. -/
lemma loop_contradiction
    (L        : ℕ → Bool)
    (hComp    : Computable L)
    (hExt     : ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
                  L (Encodable.encode c₁) = L (Encodable.encode c₂))
    (cFalse cTrue : Code)                         -- “bad” vs “good” witnesses
    (hFalse : L (Encodable.encode cFalse) = false)
    (hTrue  : L (Encodable.encode cTrue)  = true) : False := by
  -- 1 ▸ translate the witness bits into the classifier language
  have bit_false :
      (Φ L).C (Numbering.decode (Encodable.encode cFalse)) = false := by
    simpa [Φ, Numbering.decode_encode] using hFalse
  have bit_true  :
      (Φ L).C (Numbering.decode (Encodable.encode cTrue)) = true := by
    simpa [Φ, Numbering.decode_encode] using hTrue

  -- 2 ▸ apply the generic diagonal engine
  exact
    Kleene.UCI.Classifier.uciGeneral (D := ℕ)
      (Φ L)                       -- classifier
      (Φ_comp hComp)              -- computability
      (by                          -- decoder ℕ → ℕ is computable
        simpa using (Computable.id : Computable (fun n : ℕ => n)))
      (Φ_ext hExt)                -- extensionality
      cFalse cTrue                -- witnesses (bad , good)
      bit_false bit_true

/-- **Public-facing theorem**: there is no total computable self-loop decider
    that is both extensionally correct *and* non-trivial.                 -/
theorem no_total_loop_decider :
  ¬ ∃ (L : ℕ → Bool),
        Computable L ∧
        (∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
             L (Encodable.encode c₁) = L (Encodable.encode c₂)) ∧
        (∃ iF : ℕ, L iF = false) ∧
        (∃ iT : ℕ, L iT = true) := by
  rintro ⟨L, hComp, hExt, ⟨iF, hF⟩, ⟨iT, hT⟩⟩
  -- Turn numeric witnesses into `Code`s
  let cFalse : Code := numToCode iF
  let cTrue  : Code := numToCode iT
  -- Rewrite the bits at the encoded Codes
  have hFalse' : L (Encodable.encode cFalse) = false := by
    simpa [cFalse, numToCode_encode] using hF
  have hTrue'  : L (Encodable.encode cTrue) = true := by
    simpa [cTrue, numToCode_encode] using hT
  -- Invoke the contradiction lemma
  exact loop_contradiction L hComp hExt cFalse cTrue hFalse' hTrue'

end TimeLoopUCI
