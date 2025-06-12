import Impossibility.Evolution
import Mathlib.Computability.PartrecCode
import Mathlib.Logic.Encodable.Basic

open Classical Evolution Nat.Partrec Code

namespace CatTailWitness


/-- The “add-one” function n ↦ n + 1. -/
def succDef : ℕ → ℕ := Nat.succ

/-- The code that realises `succDef`. -/
def succCode : Code := Code.succ

/-- Gödel-encoded state corresponding to `succCode`. -/
def diagState : ℕ := Encodable.encode succCode

/-- `succCode` indeed yields n + 1 on input n. -/
lemma eval_succ (n : ℕ) :
    succCode.eval n = pure (succDef n) := by
  simp [succCode, succDef, Code.eval]

/-- **Reactivity lemma**: in any evolution `E`, its `F` behaves like
    `succDef` when started from `diagState`. -/
lemma F_behaves_like_succ {E : Evolution} (n : ℕ) :
    E.F diagState n = succDef n := by
  have hEval : succCode.eval n = pure (succDef n) := eval_succ n
  simpa [diagState] using (E.reacts hEval)

end CatTailWitness
