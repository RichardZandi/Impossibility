import Impossibility.SentenceManualNumberingGodel

/-!
FirstOrderSemantics.lean
=======================
Semantics for the Gödel‑ready syntax defined in
`SentenceManualNumberingGodel.lean`.  We interpret formulas in the
standard model ℕ with the usual arithmetic operations.

Key pieces:
* `Env`      – de Bruijn *level* environment (ℕ → ℕ).
* `evalTm`   – evaluates a term under an environment.
* `Truth`    – inductively computes the truth of a sentence.

We deliberately keep everything non‑computable (using classical logic)
so that proofs remain straightforward.
-/

open SentenceCode
open SentenceCode.Tm
open SentenceCode.Sentence

/- ## Environment -------------------------------------------------------- -/
/-- A variable environment maps each de Bruijn *level* `n` to a natural
    number.  Level 0 is the *nearest* binder. -/
abbrev Env := ℕ → ℕ

/- ## Term evaluation ---------------------------------------------------- -/
@[simp] noncomputable
def evalTm (v : Env) : Tm → ℕ
| var n        => v n
| c0           => 0
| succ t       => Nat.succ (evalTm v t)
| plus t u     => evalTm v t + evalTm v u
| times t u    => evalTm v t * evalTm v u

/- ## Semantics of formulas --------------------------------------------- -/
mutual
  noncomputable
  def Truth (v : Env) : Sentence → Prop
  | falsum        => False
  | eq t u        => evalTm v t = evalTm v u
  | lt t u        => evalTm v t < evalTm v u
  | not φ         => ¬ Truth v φ
  | and φ ψ       => Truth v φ ∧ Truth v ψ
  | or  φ ψ       => Truth v φ ∨ Truth v ψ
  | imp φ ψ       => Truth v φ → Truth v ψ
  | all φ         => ∀ n : ℕ, Truth (extend v n) φ
  | ex  φ         => ∃ n : ℕ, Truth (extend v n) φ

  /-- Extend an environment for a newly‑bound variable (level 0). -/
  -- Level 0 gets `n`; higher levels shift by 1.
  noncomputable
  def extend (v : Env) (n : ℕ) : Env
  | 0     => n
  | k+1   => v k
end

attribute [simp] Truth extend

/- ## Shorthand: Truth of closed sentences ------------------------------ -/
/-- Evaluate a *closed* sentence (no free variables) in the standard
    model ℕ under the empty environment. -/
@[simp] noncomputable def TruthClosed (φ : ClosedSentence) : Prop :=
  Truth (fun _ => 0) φ

/-!
`TruthClosed` is the key predicate later files will depend on (e.g.,
when defining a primitive‑recursive set of theorems).  The mutual block
ensures Lean treats `Truth` and `extend` as a single recursion.
-/
