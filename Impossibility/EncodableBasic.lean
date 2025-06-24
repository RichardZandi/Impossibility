import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Partrec
import Mathlib.Logic.Equiv.Basic

namespace EncodeBasic

noncomputable
instance primcodablePiFin
    {α β : Type*} [Fintype α] [Primcodable β] :
    Primcodable (α → β) :=
by
  let k : ℕ := Fintype.card α
  let eα : α ≃ Fin k := Fintype.equivFin α
  let e : (α → β) ≃ (Fin k → β) :=
    { toFun   := fun f i => f (eα.symm i)
    , invFun  := fun g a => g (eα a)
    , left_inv  := by
        intro f; funext a; simp [eα.symm_apply_apply]
    , right_inv := by
        intro g; funext i; simp [eα.apply_symm_apply] }
  exact Primcodable.ofEquiv _ e


end EncodeBasic
