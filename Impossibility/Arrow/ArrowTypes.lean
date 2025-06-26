import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace ArrowTypes

variables {σ : Type}

/-- Weak preference order (reflexive, total, transitive). -/
structure pref_order (σ : Type) :=
(R      : σ → σ → Prop)
(refl   : ∀ x, R x x)
(total  : ∀ x y, R x y ∨ R y x)
(trans  : ∀ x y z, R x y → R y z → R x z)

/-- Strict preference derived from `R`. -/
def P {σ} (r : pref_order σ) (x y : σ) : Prop :=
r.R x y ∧ ¬ r.R y x

/-- `b` is strictly best inside finite set `X` w.r.t. order `r`. -/
def is_strictly_best  {σ} (b : σ) (r : pref_order σ) (X : Finset σ) : Prop :=
∀ a ∈ X, a ≠ b → P r b a

/-- `b` is strictly worst inside `X`. -/
def is_strictly_worst {σ} (b : σ) (r : pref_order σ) (X : Finset σ) : Prop :=
∀ a ∈ X, a ≠ b → P r a b

/-- Either strictly best or strictly worst. -/
def is_extremal     {σ} (b : σ) (r : pref_order σ) (X : Finset σ) : Prop :=
is_strictly_worst b r X ∨ is_strictly_best b r X

def same_order {σ} (r₁ r₂ : pref_order σ) (x y : σ) : Prop :=
(P r₁ x y ∧ P r₂ x y) ∨ (P r₁ y x ∧ P r₂ y x)

end ArrowTypes
