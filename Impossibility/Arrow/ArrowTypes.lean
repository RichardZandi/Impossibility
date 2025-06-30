import Mathlib.Data.Finset.Card
import Mathlib.Tactic


namespace ArrowTypes

universe u

/-- Weak preference order (reflexive, total, transitive). -/
structure pref_order (α : Type u) : Type u where
R      : α → α → Prop
refl   : ∀ x, R x x
total  : ∀ x y, R x y ∨ R y x
trans  : ∀ x y z, R x y → R y z → R x z

/-- Strict preference derived from R. -/
def P {α : Type u} (r : pref_order α) (x y : α) : Prop :=
r.R x y ∧ ¬ r.R y x

/-- b is strictly best inside finite set X w.r.t. order r. -/
def is_strictly_best {α : Type u} (b : α) (r : pref_order α) (X : Finset α) : Prop :=
∀ a ∈ X, a ≠ b → P r b a

/-- b is strictly worst inside X. -/
def is_strictly_worst {α : Type u} (b : α) (r : pref_order α) (X : Finset α) : Prop :=
∀ a ∈ X, a ≠ b → P r a b

/-- Either strictly best or strictly worst. -/
def is_extremal {α : Type u} (b : α) (r : pref_order α) (X : Finset α) : Prop :=
is_strictly_worst b r X ∨ is_strictly_best b r X

/-- Two orders agree on the relative ranking of x, y. -/
def same_order {α : Type u} (r₁ r₂ : pref_order α) (x y : α) : Prop :=
(P r₁ x y ∧ P r₂ x y) ∨ (P r₁ y x ∧ P r₂ y x)

/-- Trivial (indifferent) preference. -/
def constTrue {α : Type u} : pref_order α :=
{ R      := λ _ _ => True
, refl   := λ _ => trivial
, total  := λ _ _ => Or.inl trivial
, trans  := λ _ _ _ _ _ => trivial }

/-- Linear preference: a weak order plus antisymmetry. -/
structure lin_pref_order (α : Type u) extends pref_order α where
antisymm : ∀ {x y}, R x y → R y x → x = y

/-- Coercion: forget antisymmetry. -/
instance {α : Type u} : Coe (lin_pref_order α) (pref_order α) where
coe p := { R := p.R, refl := p.refl, total := p.total, trans := p.trans }

/-- Strict order from a linear preference. -/
@[inline] def linP {α : Type u} (p : lin_pref_order α) (x y : α) : Prop :=
p.R x y ∧ ¬ p.R y x

/-- Register totality for p.R. -/
instance {α : Type u} (p : lin_pref_order α) : IsTotal α p.R where total := p.total

/-- Register transitivity for p.R. -/
instance {α : Type u} (p : lin_pref_order α) : IsTrans α p.R where trans := p.trans

end ArrowTypes


