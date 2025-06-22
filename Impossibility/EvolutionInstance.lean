/-
EvolutionInstance.lean
----------------------

## Purpose
A single, reusable `Evolution` object that many diagonal‑style impossibility
proofs can import.  It packages a **total but non‑computable** universal
evaluator together with an `[ExtensionalF]` instance.  Proof files such as

* `GodelImpossibility.lean`
* `HaltingUCI.lean`
* `PZIEscape.lean`
* any Cat‑and‑Tail style construction

can simply write:

```lean
import Impossibility.EvolutionInstance
open EvolutionInstance

noncomputable def E0 : Evolution := (E 0)   -- totalises with default 0
```

and immediately obtain a fully‑fledged `Evolution` plus its extensional
evidence.

### Interface

```
evalTotal (d idx n) : ℕ
E d                 : Evolution
[ExtensionalF (E d)]
```

* `d : ℕ` is the value returned when the underlying program diverges.
  Most proofs choose `d = 0`, but any constant works.

### No dependency on
* measure‑theoretic context,
* or the particular impossibility theorem.

So there is only **one** copy of this plumbing in the entire code‑base.
-/

import Impossibility.Evolution
import Godelnumbering.Transport            -- `numToCode`, `numToCode_encode`
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Part

open Classical
open Nat.Partrec Code Godel

namespace EvolutionInstance

/-! ### 1.  Total wrapper around partial evaluation -/
namespace Part

/-- `getD p d` returns the value inside `p` if it halts,
    otherwise the supplied default `d`. -/
noncomputable def getD {α} (p : Part α) (d : α) : α := by
  by_cases h : p.Dom
  · exact p.get h
  · exact d

@[simp] lemma getD_some {α} (a d : α) : getD (Part.some a) d = a := by
  simp [getD]

end Part
open Part

/-! ### 2.  A universal total evaluator -/

/--
`evalTotal d idx n` runs the program whose Gödel code is `idx`
on input `n`.  If the program diverges we return the constant
`d`.

* The function is **total** for every choice of `d`.
* It is **not computable** (classical recursion‑theory result).

Most users fix `d = 0`.
-/
noncomputable def evalTotal (d idx n : ℕ) : ℕ :=
  Part.getD ((numToCode idx).eval n) d

/-! ### 3.  Building a reusable `Evolution` object -/

/--
`E d` is a value of type `Evolution` whose transition function
is `evalTotal d`.
-/
noncomputable def E (d : ℕ) : Evolution where
  F      := evalTotal d
  reacts := by
    intro c n y h    -- `h : c.eval n = pure y`
    simp [evalTotal, h]

/-! ### 4.  Extensional evidence -/

/--
`[ExtensionalF (E d)]` — if two codes compute the same partial
function, then `F` cannot distinguish them.

The proof works for **all** `d`; therefore we declare a single
instance indexed by `d`.
-/
instance (d : ℕ) : ExtensionalF (E d) := by
  constructor
  intro c₁ c₂ hEq n
  have h :
      Part.getD (c₁.eval n) d =
      Part.getD (c₂.eval n) d :=
    congrArg (fun f : ℕ → Part ℕ ↦ Part.getD (f n) d) hEq
  simpa [E, evalTotal, numToCode_encode, Encodable.encode] using h

/-! ### 5.  Quick‑start guide

```lean
import Impossibility.EvolutionInstance
open EvolutionInstance

-- Choose any default constant.  Zero is conventional.
noncomputable def MyE : Evolution := (E 0)

-- The extensional instance is already in scope:
#synth ExtensionalF MyE
```
-/

end EvolutionInstance
