/-
HaltingEvolution.lean
---------------------

A *fully constructive* `Evolution` tailored to the Halting-problem diagonal
argument.

* `F idx n` runs program `idx` on input `n`; if it halts we return its output,
  otherwise we default to `0`.  This makes `F` total.  Because it uses
  `Part.get`, `F` is **not** computable, so we supply **only**
  `[ExtensionalF E]` (not `[ComputableF E]`).

No admits, no sorrys.
-/

import Impossibility.Evolution
import Godelnumbering.Transport            -- numToCode, numToCode_encode
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Part

open Classical Nat.Partrec Code Godel

/-! ### 1  A total wrapper for partial evaluation -/
namespace Part

/-- `getD p d` returns the value inside `p` if it halts (`Part.some a`),
    otherwise the provided default `d`. -/
noncomputable def getD {α} (p : Part α) (d : α) : α := by
  by_cases h : p.Dom
  · exact p.get h
  · exact d

@[simp] lemma getD_some {α} (a d : α) : getD (Part.some a) d = a := by
  simp [getD]

end Part
open Part

/-! ### 2  Total evaluator -/

/-- `evalTotal idx n` ≔  program `idx` on input `n`, default `0` if it diverges. -/
noncomputable def evalTotal (idx n : ℕ) : ℕ :=
  Part.getD ((numToCode idx).eval n) 0   -- total but non-computable

/-! ### 3  Evolution structure -/
noncomputable def E : Evolution where
  F := evalTotal
  reacts := by
    intro c n y h            -- `h : c.eval n = pure y`
    simp [evalTotal, Encodable.encode, h]

/-! ### 4  Extensionality instance (optional evidence) -/
instance : ExtensionalF E := by
  constructor
  intro c₁ c₂ hEq n
  -- Wrap both sides of the functional equality with `Part.getD … 0`
  have h : Part.getD (c₁.eval n) 0 = Part.getD (c₂.eval n) 0 :=
    congrArg (fun f : ℕ → Part ℕ => Part.getD (f n) 0) hEq
  -- Rewrite the goal to the same shape using `numToCode_encode`.
  simpa [E, evalTotal, numToCode_encode, Encodable.encode] using h
