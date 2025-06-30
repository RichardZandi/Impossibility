/-
RussellUCI.lean
───────────────
UCI-style derivation of Russell’s paradox (“the set of all sets
that do not contain themselves”) formalised with Lean 4.

Domain Ω      : codes of Lean `Set Bool` -valued predicates.
Classifier C  : “does the coded predicate hold of its own code?”
Diagonal d    : predicate R := λ x, ¬ (C x x)
Feedback      : R refers to C, C refers to R  → contradiction.
-/

import Impossibility.UCICoreTest
import Impossibility.Halting.HaltingUCI
import Impossibility.EvolutionInstance
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Bool.Basic
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances
import Kleene2.KleeneFix

open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier
open EvolutionInstance   -- gives us `haltCode`, `divergeCode` if you `open` your other file
open HaltingUCI

namespace RussellUCI

/-- bundle `e ↦ C e e` as a classifier -/
noncomputable def Φ (C : ℕ → ℕ → Bool) : Classifiers ℕ :=
  ⟨fun e => C e e⟩

/-- computability of that classifier -/
lemma Φ_comp {C : ℕ → ℕ → Bool}
    (hComp : Computable (fun p : ℕ × ℕ => C p.1 p.2)) :
    Computable (fun e => C e e) := by
  have h_pair : Computable (fun e : ℕ => (e, e)) :=
    (Computable.pair Computable.id Computable.id)
  simpa using (Computable.comp hComp h_pair)

/-- diagonal contradiction for one concrete enumerator `C` -/
lemma russell_contradiction
    (C       : ℕ → ℕ → Bool)
    (hComp   : Computable (fun p : ℕ × ℕ => C p.1 p.2))
    (hExt    :
       ∀ {c₁ c₂ : Code},
         c₁.eval = c₂.eval →
         C (Encodable.encode c₁) (Encodable.encode c₁) =
         C (Encodable.encode c₂) (Encodable.encode c₂))
    (badCode goodCode : Code)
    (hBadBit  : C (Encodable.encode badCode)  (Encodable.encode badCode)  = false)
    (hGoodBit : C (Encodable.encode goodCode) (Encodable.encode goodCode) = true) :
    False := by
  -- witnesses in exactly the shape uciGeneral wants
  have bit_false : (fun e => C e e) (Encodable.encode badCode)  = false := hBadBit
  have bit_true  : (fun e => C e e) (Encodable.encode goodCode) = true  := hGoodBit

  -- extensionality rewritten for the classifier
  have hExt_on_codes :
      ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
        (fun e => C e e) (Encodable.encode c₁) =
        (fun e => C e e) (Encodable.encode c₂) := @hExt

  -- drive the generic contradiction
  exact
    Kleene.UCI.Classifier.uciGeneral (D := ℕ)
      (Φ C)
      (Φ_comp (C := C) hComp)
      (by
        simpa using (Computable.id : Computable (fun n : ℕ => n))) -- decoder ℕ→ℕ
      hExt_on_codes
      badCode     -- bad  : Code
      goodCode    -- good : Code
      bit_false
      bit_true

/-- headline impossibility theorem -/
theorem no_total_injective_pred_enumerator :
  ¬ ∃ (C : ℕ → ℕ → Bool),
       Computable (fun p : ℕ × ℕ => C p.1 p.2) ∧
       (∀ {c₁ c₂ : Code},
          c₁.eval = c₂.eval →
          C (Encodable.encode c₁) (Encodable.encode c₁) =
          C (Encodable.encode c₂) (Encodable.encode c₂)) ∧
       (∃ badCode  : Code,
          C (Encodable.encode badCode)  (Encodable.encode badCode)  = false) ∧
       (∃ goodCode : Code,
          C (Encodable.encode goodCode) (Encodable.encode goodCode) = true) := by
  rintro ⟨C, hComp, hExt, ⟨badCode, hBad⟩, ⟨goodCode, hGood⟩⟩
  exact russell_contradiction C hComp hExt badCode goodCode hBad hGood

end RussellUCI
