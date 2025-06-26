import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Computability.Partrec
import Impossibility.EncodableBasic

open Classical Primrec
open Encodable
open EncodeBasic


namespace PrefCodec

/-! 0 ▸  A *generic* `Primcodable` for **any** finite type `A`.          -/
noncomputable
instance primcodableOfFintype (A : Type*) [Fintype A] : Primcodable A :=
  -- `Fin (card A)` already has `Primcodable`; transport along the equivalence
  Primcodable.ofEquiv _ (Fintype.equivFin A)


/-! 1 ▸  Boolean *matrix* on `A`.                                        -/
abbrev PrefMat (A : Type*) := (A × A) → Bool

/-! 2 ▸  Profile of such matrices, one voter for every `Fin k`.          -/
abbrev ProfileMat (α A : Type*) [Fintype α] := Fin (Fintype.card α) → PrefMat A

noncomputable instance prefMatPrim {A} [Fintype A] :
    Primcodable (PrefMat A) :=
  -- domain is  A × A ,  codomain is Bool
  EncodeBasic.primcodablePiFin (α := A × A) (β := Bool)

noncomputable
instance profileMatPrim {α A} [Fintype α] [Fintype A] :
    Primcodable (ProfileMat α A) :=
  -- domain is  Fin (card α) ,  codomain is PrefMat A
  EncodeBasic.primcodablePiFin
    (α := Fin (Fintype.card α)) (β := PrefMat A)

/-! 4 ▸  Smoke test ----------------------------------------------------- -/
#synth Primcodable (PrefMat (Fin 3))
#synth Primcodable (ProfileMat (Fin 2) (Fin 3))

end PrefCodec
