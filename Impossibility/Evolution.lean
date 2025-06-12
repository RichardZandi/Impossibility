/-
# `Evolution` — a generic reactive–system abstraction
   for UCI-style diagonal proofs

The core interface is intentionally minimal:

* `F      : ℕ → ℕ → ℕ`     – next-state / output function;
* `reacts`                – semantic-transparency bridge from `Code.eval`
                            to system dynamics.

**Optional evidence** is supplied via *type-classes*:

* `ComputableF E`  – a proof that `F` is total computable;
* `ExtensionalF E` – extensionality with respect to code equivalence.

Projects prove these instances when needed; otherwise they simply omit
them—no `admit`, no `sorry`, and no axioms in the base definition.
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Logic.Encodable.Basic

open Classical Nat.Partrec Code
set_option autoImplicit false

/-- A deterministic, Gödel-encodable reactive system. -/
structure Evolution where
  /-- System transition / output function. -/
  F      : ℕ → ℕ → ℕ
  /-- **Reactivity (semantic transparency).**
      If a code `c` halts with value `y` on input `n`, then starting the
      system from state `encode c` and feeding the same input must also
      yield `y`. -/
  reacts :
    ∀ {c : Code} {n y : ℕ},
      c.eval n = pure y →
      F (Encodable.encode c) n = y

/-- Optional evidence that `E.F` is total computable. -/
class ComputableF (E : Evolution) : Prop where
  comp : Computable (fun p : ℕ × ℕ => E.F p.1 p.2)

/-- Optional **extensionality**: codes with identical semantics lead to
    identical system behaviour. -/
class ExtensionalF (E : Evolution) : Prop where
  ext :
    ∀ {c₁ c₂ : Code}, (c₁.eval = c₂.eval) →
      ∀ n, E.F (Encodable.encode c₁) n =
           E.F (Encodable.encode c₂) n

namespace Evolution

/-- A **predictor** for an evolution `F`: a total computable function that
    claims perfect foresight `F s (pred s) = pred s` for every state. -/
structure Predictor (F : ℕ → ℕ → ℕ) where
  pred    : ℕ → ℕ
  hComp   : Computable pred
  perfect : ∀ s : ℕ, F s (pred s) = pred s

end Evolution
