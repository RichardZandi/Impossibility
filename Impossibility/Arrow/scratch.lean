import Mathlib.Data.Fintype.Basic        -- Fintype, Fin n
import Mathlib.Tactic.FinCases   -- for `fin_cases`
import Mathlib.Data.Fintype.Prod   -- ← NEW
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Mathlib.Computability.Partrec
import Mathlib.Order.RelClasses
import Mathlib.Computability.Primrec
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Vector.Basic

namespace EncodeBasic

open List
open Finset
open Classical
open Nat
open Option
open Encodable
open Primrec
open scoped Function

@[inline] def pair   := Nat.pair
@[inline] def unpair := Nat.unpair

theorem unpair_pair (a b : ℕ) : unpair (pair a b) = (a, b) := by
  simpa [pair, unpair] using Nat.unpair_pair a b

theorem pair_unpair (n : ℕ) : pair (unpair n).1 (unpair n).2 = n := by
  simpa [pair, unpair] using Nat.pair_unpair n


variable {A : Type} [Fintype A] [DecidableEq A]

private def peel {β} [Encodable β] :
    ℕ → ℕ → List β → Option (List β)
  | _, 0,     acc => some acc
  | n, k+1,   acc => do
      let (m,n') := unpair n
      let b ← decode m
      peel n' k (b :: acc)
termination_by _ k _ => k

def encodeFin2Bool (f : Fin 2 → Bool) : ℕ :=
  (List.finRange 2).foldr (fun i acc => pair (encode (f i)) acc) 0
  -- `List.finRange 2` is `[0, 1] : List (Fin 2)`

def decodeFin2Bool (n : ℕ) : Option (Fin 2 → Bool) := do
  let revBs ← peel n 2 ([] : List Bool)   -- reverse order
  let bs := revBs.reverse                 -- restore original order
  if h : bs.length = 2 then
    -- rebuild the function
    pure (fun i : Fin 2 =>
      bs.get ⟨i, by
        -- `i.isLt : (i : ℕ) < 2`; turn `2` into `bs.length` via `h`
        simpa [h] using i.isLt⟩)
  else
    none

noncomputable
def piFinEncode {α β} [Fintype α] [Encodable β] (f : α → β) : ℕ :=
  let k : ℕ := Fintype.card α
  (List.finRange k).foldr
    (fun (i : Fin k) acc =>
       let a : α := (Fintype.equivFin α).symm i
       pair (encode (f a)) acc)
    0

noncomputable
def piFinDecode {α β} [Fintype α] [Encodable β] (n : ℕ) :
    Option (α → β) := by
  let k : ℕ := Fintype.card α
  match peel n k ([] : List β) with
  | none        => exact none
  | some revBs  =>
      let bs := revBs.reverse
      if hlen : bs.length = k then
        let g : α → β := fun a =>
          let i : Fin k := (Fintype.equivFin α) a
          have : (i : ℕ) < bs.length := by
            simpa [hlen] using i.isLt
          bs.get ⟨i, this⟩
        exact some g
      else
        exact none

lemma decode_list_length
    {α β} [Fintype α] [Encodable β] (f : α → β) :
  (((List.finRange (Fintype.card α)).map
        (fun i : Fin (Fintype.card α) =>
          f ((Fintype.equivFin α).symm i))).reverse).length
    = Fintype.card α := by
  simp [List.length_reverse, List.length_map, List.length_finRange]


lemma rebuild_eq
    {α β} [Fintype α] [Encodable β] (f : α → β) :
  (fun a : α =>
     let i : Fin (Fintype.card α) := (Fintype.equivFin α) a
     f ((Fintype.equivFin α).symm i)) = f := by
  funext a
  have : (Fintype.equivFin α).symm ((Fintype.equivFin α) a) = a :=
    Equiv.symm_apply_apply (Fintype.equivFin α) a
  simpa using congrArg f this


lemma peel_encodes
    {α β} [Fintype α] [Encodable β] (f : α → β) :
  peel (piFinEncode f) (Fintype.card α) ([] : List β) =
    some (((List.finRange (Fintype.card α)).map
             (fun i : Fin (Fintype.card α) =>
               f ((Fintype.equivFin α).symm i))).reverse) := by
  let k := Fintype.card α
  have hAcc :
      ∀ (l : List (Fin k)) (acc : List β),
        peel
          (l.foldr
              (fun i acc' =>
                 pair (encode (f ((Fintype.equivFin α).symm i))) acc')
              0)
          l.length
          acc
        =
        some ((l.reverse.map (fun i => f ((Fintype.equivFin α).symm i))) ++ acc) := by
    intro l
    induction l with
    | nil =>
        intro acc; simp [peel]
    | cons i t ih =>
        intro acc
        simp [peel, ih, List.foldr_cons, List.reverse_cons,
              unpair_pair, encodek]
  simpa [piFinEncode] using hAcc (List.finRange k) []

lemma piFinRoundTrip
    {α β} [Fintype α] [Encodable β] (f : α → β) :
  piFinDecode (piFinEncode f) = some f := by
  let k : ℕ := Fintype.card α
  have hPeel := peel_encodes  (f := f)
  have hLen  := decode_list_length (f := f)
  dsimp [piFinDecode]
  simp [hPeel]


noncomputable
instance piFinEncodable {α β} [Fintype α] [Encodable β] :
    Encodable (α → β) where
  encode  := piFinEncode
  decode  := piFinDecode
  encodek := piFinRoundTrip

open scoped Function
open Encodable

/-!  Primcodable instance for finite function spaces (α → β)  -/

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
    , left_inv := by
        intro f; funext a; simp [eα.symm_apply_apply]
    , right_inv := by
        intro g; funext i; simp [eα.apply_symm_apply] }
  exact Primcodable.ofEquiv _ e



end EncodeBasic


==========
import Mathlib.Order.RelClasses
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Computability.Partrec
import Impossibility.EncodableBasic
import Mathlib.Data.Fintype.Basic
import Impossibility.EncodableBasic   -- brings primcodablePiFin




namespace PrefCodec

open Classical
open scoped Function
open Encodable
open EncodeBasic


structure Preference (A : Type u) [DecidableEq A] : Type u where
  rel          : A → A → Prop
  strict_total : IsStrictTotalOrder A rel

noncomputable def defaultPreference
    {A : Type*} [Fintype A] [DecidableEq A] : Preference A :=
by
  -- Pull the relation back along the equivalence
  let rel : A → A → Prop := fun x y ↦
        (Fintype.equivFin A x) < (Fintype.equivFin A y)

  -- `RelEmbedding.preimage` gives a relation embedding
  -- and `.isStrictTotalOrder` transports the order proof in one shot.
  have h : IsStrictTotalOrder A rel :=
    (RelEmbedding.preimage
        ⟨Fintype.equivFin A, (Fintype.equivFin A).injective⟩
        (· < ·)).isStrictTotalOrder  -- :contentReference[oaicite:0]{index=0}

  exact ⟨rel, h⟩

noncomputable instance {A} [Fintype A] [DecidableEq A] :
    Inhabited (Preference A) := ⟨defaultPreference⟩

noncomputable def encodePreference
    {A : Type} [Fintype A] [DecidableEq A]
    (p : Preference A) : ℕ :=
  encode (fun xy : A × A =>
            decide (p.rel xy.1 xy.2))

noncomputable def decodePreference
    {A : Type} [Fintype A] [DecidableEq A]
    (n : ℕ) : Option (Preference A) := do
  let b ← decode (α := (A × A) → Bool) n
  if h : IsStrictTotalOrder A (fun x y => b ⟨x, y⟩ = true) then
    pure ⟨(fun x y => b ⟨x, y⟩), h⟩
  else
    none

theorem roundtripPreference
    {A : Type} [Fintype A] [DecidableEq A]
    (p : Preference A) :
  decodePreference (encodePreference p) = some p := by
  dsimp [encodePreference, decodePreference]
  simp [encodek]                    -- uses Encodable round-trip
  have hEq :
      (fun x y : A =>
        decide (p.rel x y) = true) = p.rel := by
    funext x y; by_cases h : p.rel x y <;> simp [h]
  simpa [hEq, p.strict_total]

noncomputable instance preferenceEncodable
    {A : Type} [Fintype A] [DecidableEq A] :
    Encodable (Preference A) where
  encode  := encodePreference
  decode  := decodePreference
  encodek := roundtripPreference


open PrefCodec

noncomputable
instance preferencePrimcodable
    {A : Type*} [Fintype A] [DecidableEq A] :
    Primcodable (Preference A) :=
by
  -- identify Preference A with the subtype of Boolean matrices
  -- carrying the strict-total-order proof, then reuse Primcodable.subtype
  have e :
      Preference A ≃
        { b : (A × A) → Bool //
            IsStrictTotalOrder A (fun x y => b ⟨x, y⟩ = true) } :=
    { toFun := fun p => ⟨fun xy => decide (p.rel xy.1 xy.2), by
        -- the axioms hold because we just re-decided an existing order
        simpa using p.strict_total⟩,
      invFun := fun ⟨b, h⟩ => ⟨(fun x y => b ⟨x, y⟩ = true), by
        simpa using h⟩,
      left_inv := by
        intro p; cases p; simp,
      right_inv := by
        intro ⟨b, h⟩; simp }
  exact (inferInstance :
          Primcodable
            { b : (A × A) → Bool //
              IsStrictTotalOrder A (fun x y => b ⟨x, y⟩ = true) }).ofEquiv e


end PrefCodec
====
noncomputable def stoPred (b : (A × A) → Bool) : Bool :=
  irrPred b

lemma stoPred_prim : Primrec stoPred := by
  simpa [stoPred] using irrPred_prim

instance stoPred_pred :
    PrimrecPred (fun b : (A × A) → Bool =>
      ∀ x : A, b (x,x) = false) :=
⟨stoPred_prim⟩


======

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Computability.Partrec
import Impossibility.EncodableBasic

open Classical Primrec

noncomputable
instance matrixPrimcodable {A} [Fintype A] :
    Primcodable ((A × A) → Bool) :=
  EncodeBasic.primcodablePiFin (α := A × A) (β := Bool)

structure Preference (A : Type u) [DecidableEq A] : Type u where
  rel          : A → A → Prop
  strict_total : IsStrictTotalOrder A rel

variable {A : Type*} [Fintype A] [DecidableEq A]

-- the fixed points you want to plug into `b`
noncomputable def c₁ (i j : Fin (Fintype.card A)) : A :=
  (Fintype.equivFin A).symm i

noncomputable def c₂ (i j : Fin (Fintype.card A)) : A :=
  (Fintype.equivFin A).symm j

noncomputable def stoPred (b : (A × A) → Bool) : Bool :=
  decide (IsStrictTotalOrder A (fun x y => b (x, y) = true))

/-- asymmetry test: never `b x y = true` **and** `b y x = true` -/
def asymPred (b : (A × A) → Bool) : Bool :=
  decide (∀ x y : A, !(b (x,y) && b (y,x)))

lemma stoPred_prim : Primrec (stoPred (A := A)) := by
 sorry  -- replace with your finished proof

noncomputable instance stoPred_decidable
    (b : (A × A) → Bool) :
    Decidable (IsStrictTotalOrder A (fun x y => b (x, y) = true)) :=
  inferInstance

instance stoPred_pred :
    PrimrecPred
      (fun b : (A × A) → Bool =>
        IsStrictTotalOrder A (fun x y => b (x, y) = true)) :=
by
  -- `PrimrecPred p` is just `Primrec (fun a => decide (p a))`
  -- and `stoPred` *is* that Boolean function.
  simpa [PrimrecPred, stoPred]
    using stoPred_prim

noncomputable instance stoPred_decPred :
    DecidablePred (fun b : (A×A)→Bool =>
      IsStrictTotalOrder A (fun x y => b (x,y)=true)) :=
  by
    intro b
    classical
    infer_instance

noncomputable
instance prefMatrixPrim :
    Primcodable
      { b : (A × A) → Bool //
        IsStrictTotalOrder A (fun x y => b (x, y) = true) } :=
  Primcodable.subtype
        (α := (A × A) → Bool)
        (p  := fun b => IsStrictTotalOrder A (fun x y => b (x, y) = true))
        stoPred_pred

open Encodable

noncomputable
def prefEquiv :
    Preference A ≃
      { b : (A × A) → Bool //
        IsStrictTotalOrder A (fun x y => b (x, y) = true) } :=
{ toFun := fun p =>
    ⟨(fun xy => decide (p.rel xy.1 xy.2)),
     by simpa using p.strict_total⟩,
  invFun := fun ⟨b, h⟩ =>
    ⟨(fun x y => b (x, y) = true), by simpa using h⟩,
  left_inv := by
    intro p; cases p; simp,
  right_inv := by
    intro ⟨b, h⟩; simp }

noncomputable
instance preferencePrimcodable : Primcodable (Preference A) :=
  Primcodable.ofEquiv
    { b : (A × A) → Bool //
      IsStrictTotalOrder A (fun x y => b (x, y) = true) }
    prefEquiv       -- not .symm


=====
/-- Irreflexivity at one point. -/
def irrAt  (b : (A×A)→Bool) (x : A) : Bool :=
  !(b (x,x))

/-- Totality at two points (`x ≠ y`). -/
def totAt  (b : (A×A)→Bool) (x y : A) : Bool :=
  b (x,y) || b (y,x)

/-- Transitivity at three points. -/
def transAt (b : (A×A)→Bool) (x y z : A) : Bool :=
  (!(b (x,y)) || !(b (y,z))) || b (x,z)

/-- `irrAt` is primitive-recursive when the indices are fixed. -/
lemma irrAt_prim (x : A) :
    Primrec (fun b : (A×A)→Bool => irrAt b x) := by
  simpa [irrAt] using
    Primrec.not.comp (proj_pair x x)

/-- `totAt` is primitive-recursive for fixed indices. -/
lemma totAt_prim (x y : A) :
    Primrec (fun b : (A×A)→Bool => totAt b x y) := by
  simpa [totAt] using
    Primrec.or.comp (proj_pair x y) (proj_pair y x)

/-- `transAt` is primitive-recursive for fixed indices. -/
lemma transAt_prim (x y z : A) :
    Primrec (fun b : (A×A)→Bool => transAt b x y z) := by
  simpa [transAt, Bool.imp_iff_not_or] using
    Primrec.or.comp
      (Primrec.or.comp
        (Primrec.not.comp (proj_pair x y))
        (Primrec.not.comp (proj_pair y z)))
      (proj_pair x z)
