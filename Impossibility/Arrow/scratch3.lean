import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Computability.Primrec

universe u

/-- A toy ranking of `α` as a permutation of the finite set `Finset.univ : Finset α`. -/
structure ToyRanking (α : Type u) [Fintype α] [BEq α] where
  vec   : List α
  nodup : vec.Nodup
  perm  : vec.Perm ((Finset.univ : Finset α).toList)

namespace ToyRanking

variable {α : Type u} [Fintype α] [BEq α]

/-- Decode a `ToyRanking` back to a simple ≤-style order on `α`. -/
def toOrder (r : ToyRanking α) : α → α → Prop :=
  fun x y => r.vec.indexOf x ≤ r.vec.indexOf y

/-- Equivalence between *any* binary relation on `α` and a `ToyRanking α`. -/
noncomputable def equivToy : (α → α → Prop) ≃ ToyRanking α where
  toFun := fun _o =>
    { vec   := (Finset.univ : Finset α).toList
    , nodup := by
        -- `Finset.nodup_toList` gives `(s.toList).Nodup`
        exact Finset.nodup_toList (s := (Finset.univ : Finset α))
    , perm  := List.Perm.refl _ }
  invFun  := fun r => toOrder r
  left_inv := by intro _; sorry
  right_inv := by intro r; cases r; sorry

end ToyRanking

/-- Now we get a `Primcodable` instance “for free.” -/
noncomputable instance toyRankingPrimcodable
  {α : Type u} [Fintype α] [BEq α]
  [pt : Primcodable (α → α → Prop)] :  -- you must have this!
  Primcodable (ToyRanking α) :=
Primcodable.ofEquiv _ (Equiv.symm (ToyRanking.equivToy (α := α)))
