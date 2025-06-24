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


/-! 3 ▸  Both are *automatically* `Primcodable` via `primcodablePiFin`.  -/
noncomputable
instance prefMatPrim     {A} [Fintype A]              : Primcodable (PrefMat A) :=
  primcodablePiFin      -- domain  A×A  is `Primcodable` by step 0

noncomputable
instance profileMatPrim {α A} [Fintype α] [Fintype A] : Primcodable (ProfileMat α A) :=
  primcodablePiFin      -- domain  Fin k  already `Primcodable` in mathlib


/-! 4 ▸  Smoke test ----------------------------------------------------- -/
#synth Primcodable (PrefMat (Fin 3))
#synth Primcodable (ProfileMat (Fin 2) (Fin 3))

end PrefCodec
