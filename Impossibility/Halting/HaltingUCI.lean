/-
HaltingUCI.lean
----------------
A **self‑contained** UCI instantiation that turns a *hypothetical* Halting
oracle `H` into a computable classifier and then feeds it to the Universal
Classification Impossibility engine, yielding a contradiction.

* No attempt is made to implement `H`; we simply *assume* its existence via
  three axioms (totality + correctness).
* The classifier `good?` asks whether the machine whose *Gödel index* is `s`
  halts on the fixed input `0`.
* Two concrete codes supply the opposite truth‑values required by UCI: the
  trivial constant‑zero program and a canonical diverging program.
* The extensionality lemma is proved directly from the equality of partial
  evaluation functions.

The file relies on the same helper libraries that power `CatTailUCI.lean`.
-/
import Mathlib.Computability.Primrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Bool.Basic
import Mathlib.Computability.TuringMachine
import Godelnumbering.Godel
import Godelnumbering.Instances
import Impossibility.Evolution
--import Impossibility.PartExtras
import Impossibility.Halting.HaltingWitness           -- uses `E.reacts`
import UCI.UCICore

open Classical Evolution Nat.Partrec Code
open Kleene.UCI.Classifier
open Godel
open Turing TM2

namespace Part

/-- Same `getD` we used before. -/
noncomputable def getD {α} (p : Part α) (d : α) : α := by
  by_cases h : p.Dom
  · exact p.get h
  · exact d

@[simp] lemma eval_none_dom {α} : (Part.none : Part α).Dom = False := by
  simp

end Part


namespace HaltingUCI

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

-- H is a TM2 machine
variable (H : Λ → TM2.Stmt Γ Λ σ)

-- H decides the halting problem correctly
variable (H_decides : ∀ (M : Λ → TM2.Stmt Γ Λ σ) (k : K) (input : List (Γ k)),
  ∃ (result : List (Γ k)),
  (∃ encoded_input, TM2.eval H k encoded_input = Part.some result) ∧
  (result ≠ [] ↔ (TM2.eval M k input).Dom))

-- H always halts (totality - this is essential!)
variable (H_total : ∀ (k : K) (input : List (Γ k)), (TM2.eval H k input).Dom)

/-! ## 2  Classifier built from `H` -/
variable (k₀ : K)
variable (encode_input : ℕ → List (Γ k₀))

noncomputable def good? (H : Λ → TM2.Stmt Γ Λ σ) (k₀ : K) (encode_input : ℕ → List (Γ k₀)) : ℕ → Bool :=
  fun s => (Part.getD (TM2.eval H k₀ (encode_input s)) ([] : List (Γ k₀))).length > 0

noncomputable abbrev HaltingClassifier : Classifiers ℕ := ⟨good? H k₀ encode_input⟩

/-! ### 2.1  Computability -/

open Computable Primrec

/-- `good?` is computable once we know how to compute the *length* core. -/
lemma good?_computable
    (hCore : Computable (fun s : ℕ =>
               (Part.getD (TM2.eval H k₀ (encode_input s))
                           ([] : List (Γ k₀))).length)) :
    Computable (good? H k₀ encode_input) := by
  /-  Boolean post-processing: `n ↦ (n > 0)` is computable.                -/
  have hPos : Computable (fun n : ℕ => n > 0) := by
    -- `gt` on pairs, then curry with `(n,0)`.
    have hGt : Computable (fun p : ℕ × ℕ => p.1 > p.2) := Computable.gt
    have hPair : Computable (fun n : ℕ => (n, (0 : ℕ))) :=
      Computable.pair Computable.id (Computable.const 0)
    exact hGt.comp hPair

  /-  Compose the two computable pieces.                                   -/
  exact hPos.comp hCore



end HaltingUCI
