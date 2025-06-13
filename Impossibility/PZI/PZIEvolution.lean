/-
PZIEvolution.lean
-----------------

A *fully constructive* `Evolution` intended for the Prefix–Zero-Set
Impossibility (PZI) diagonal argument.

*  `F idx n` runs program `idx` on input `n`.
   If it halts we return the output; otherwise we default to `0`.
   This makes `F` total but **not computable**.

Exactly as in `HaltingEvolution.lean` we provide **only** the
`[ExtensionalF E]` instance – no `[ComputableF E]`.

No `admit`, no `sorry`.
-/

import Impossibility.Evolution
import Godelnumbering.Transport            -- numToCode, numToCode_encode
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Part

open Classical
open Nat.Partrec Code Godel

/-! ### 1  A total wrapper for partial evaluation -/
namespace Part

/-- `getD p d` returns the value inside `p` if it halts,
    otherwise the default `d`. -/
noncomputable def getD {α} (p : Part α) (d : α) : α := by
  by_cases h : p.Dom
  · exact p.get h
  · exact d

@[simp] lemma getD_some {α} (a d : α) : getD (Part.some a) d = a := by
  simp [getD]

end Part
open Part

/-! ### 2  Total evaluator -/

/-- `evalTotal idx n` ≔ run program `idx` on input `n`,
    default to `0` when it diverges. -/
noncomputable def evalTotal (idx n : ℕ) : ℕ :=
  Part.getD ((numToCode idx).eval n) 0     -- total (but not computable)

/-! ### 3  Evolution structure -/
noncomputable def PZIE : Evolution where
  F      := evalTotal
  reacts := by
    intro c n y h            -- `h : c.eval n = pure y`
    simp [evalTotal, Encodable.encode, h]

/-! ### 4  Extensional-evidence instance -/
instance : ExtensionalF PZIE := by
  constructor
  intro c₁ c₂ hEq n
  -- Wrap the functional equality with `Part.getD … 0`.
  have h :
      Part.getD (c₁.eval n) 0 =
      Part.getD (c₂.eval n) 0 :=
    congrArg (fun f : ℕ → Part ℕ => Part.getD (f n) 0) hEq
  -- Rewrite both sides into the `evalTotal` form.
  simpa [PZIE, evalTotal, numToCode_encode, Encodable.encode] using h
