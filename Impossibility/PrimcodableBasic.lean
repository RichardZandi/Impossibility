import Mathlib.Data.Fintype.Basic        -- Fintype, Fin n
import Mathlib.Algebra.Order.Ring.Nat    -- ℕ, Nat.sqrt for unpair
import Mathlib.Data.Finset.Basic   -- for `Finset.toList`
import Mathlib.Tactic.FinCases   -- for `fin_cases`
import Mathlib.Data.Fintype.Prod   -- ← NEW
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.DeriveFintype   -- provides the handler
import Mathlib.Tactic

/-! ### A minimal “Primcodable” library from scratch -/

namespace MyCompute

open List         -- for unfoldr? and List.foldl
open Finset       -- for `toList`
open Classical
open Nat
open Option

/-- A Cantor‐pairing function.  We just reuse `Nat.pair`. -/
@[inline] def pair   := Nat.pair
/-- Its inverse.  Alias of `Nat.unpair`. -/
@[inline] def unpair := Nat.unpair

theorem unpair_pair (a b : ℕ) : unpair (pair a b) = (a, b) := by
  simpa [pair, unpair] using Nat.unpair_pair a b

theorem pair_unpair (n : ℕ) : pair (unpair n).1 (unpair n).2 = n := by
  simpa [pair, unpair] using Nat.pair_unpair n


/-- Our own Primcodable class.  You can think of it as “Encodable + round‐trip.” -/
class Primcodable (α : Type) where
  encode    : α → ℕ
  decode    : ℕ → Option α
  roundtrip : ∀ x, decode (encode x) = some x

namespace Primcodable

/-- ℕ is trivially Primcodable. -/
instance nat : Primcodable ℕ where
  encode := id
  decode n := some n
  roundtrip _ := rfl

/-- Bool as 0/1. -/
instance bool : Primcodable Bool where
  encode b := if b then 1 else 0
  decode n := match n with | 0 => some false | 1 => some true | _ => none
  roundtrip b := by
    -- now `b : Bool` is in the context
    cases b <;> rfl

instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) where
  encode p := pair (encode p.1) (encode p.2)

  decode n :=
    let (a, b) := unpair n
    match decode a, decode b with
    | some x, some y => some (x, y)
    | _,        _    => none

  roundtrip := by
    intro ⟨x, y⟩
    dsimp [encode, decode]
    -- h₀ : unpair (pair (encode x) (encode y)) = (encode x, encode y)
    let h₀ := unpair_pair (encode x) (encode y)
    -- split it into fst‐ and snd‐equalities
    let h₁ : (unpair (pair (encode x) (encode y))).1 = encode x :=
      congrArg Prod.fst h₀
    let h₂ : (unpair (pair (encode x) (encode y))).2 = encode y :=
      congrArg Prod.snd h₀
    -- rewrite each projection before decoding
    rw [h₁, h₂]
    -- now match (decode (encode x)), (decode (encode y))
    let r1 := Primcodable.roundtrip (x := x)
    let r2 := Primcodable.roundtrip (x := y)
    simp [r1, r2]


instance piFin2 {β : Type} [inst : Primcodable β] : Primcodable (Fin 2 → β) where

  encode f :=
    pair (inst.encode (f 0)) (inst.encode (f 1))

  decode n :=
    let (n0, n1) := unpair n
    match inst.decode n0, inst.decode n1 with
    | some x0, some x1 =>
        some (fun
              | (0 : Fin 2) => x0
              | (1 : Fin 2) => x1)
    | _, _ => none

  roundtrip f := by
    dsimp [encode, decode]

    -- cancel the Cantor pairing
    have hp :
        unpair (pair (inst.encode (f 0)) (inst.encode (f 1)))
          = (inst.encode (f 0), inst.encode (f 1)) :=
      unpair_pair _ _

    -- rewrite decodes with `hp` and the β-round-trips; the goal becomes
    -- `some (λ …) = some f`
    simp [ hp
         , inst.roundtrip (f 0)
         , inst.roundtrip (f 1) ]       -- goal: (λ i, …) = f

    -- show the two functions are equal
    funext i
    fin_cases i                           -- i is either 0 or 1
    all_goals rfl


/- **Your** Preference type, hand‐encoded as a Boolean matrix on `A×A`. -/
variable {A : Type} [Fintype A] [DecidableEq A]


private def peel {β} [Primcodable β] :
    ℕ → ℕ → List β → Option (List β)
  | _, 0,     acc => some acc
  | n, k+1,   acc => do
      let (m,n') := unpair n
      let b ← Primcodable.decode m
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

/-- Encode `f : α → β` by enumerating α in the **`equivFin` order**. -/
noncomputable
def piFinEncode {α β} [Fintype α] [Primcodable β] (f : α → β) : ℕ :=
  let k : ℕ := Fintype.card α
  (List.finRange k).foldr
    (fun (i : Fin k) acc =>
       -- i is a Fin, so just use it
       let a : α := (Fintype.equivFin α).symm i
       pair (encode (f a)) acc)
    0


noncomputable
def piFinDecode {α β} [Fintype α] [Primcodable β] (n : ℕ) :
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
    {α β} [Fintype α] [Primcodable β] (f : α → β) :
  (((List.finRange (Fintype.card α)).map
        (fun i : Fin (Fintype.card α) =>
          f ((Fintype.equivFin α).symm i))).reverse).length
    = Fintype.card α := by
  -- `map` and `reverse` do not change length; `finRange` has length `n`.
  simp [List.length_reverse, List.length_map, List.length_finRange]



lemma rebuild_eq
    {α β} [Fintype α] [Primcodable β] (f : α → β) :
  (fun a : α =>
     let i : Fin (Fintype.card α) := (Fintype.equivFin α) a
     f ((Fintype.equivFin α).symm i)) = f := by
  funext a
  -- `Equiv.symm_apply_apply` gives `(e.symm (e a)) = a`
  have : (Fintype.equivFin α).symm ((Fintype.equivFin α) a) = a :=
    Equiv.symm_apply_apply (Fintype.equivFin α) a
  -- apply `f` to both sides
  simpa using congrArg f this


lemma peel_encodes
    {α β} [Fintype α] [Primcodable β] (f : α → β) :
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
              unpair_pair, Primcodable.roundtrip]
  simpa [piFinEncode] using hAcc (List.finRange k) []

lemma piFinRoundTrip
    {α β} [Fintype α] [Primcodable β] (f : α → β) :
  piFinDecode (piFinEncode f) = some f := by
  let k : ℕ := Fintype.card α
  have hPeel := peel_encodes  (f := f)
  have hLen  := decode_list_length (f := f)

  dsimp [piFinDecode]      -- expose the `match` and the `if`
  simp [hPeel]             -- eliminates the `match`

noncomputable
instance piFintype
    {α β} [Fintype α] [Primcodable β] : Primcodable (α → β) where
  encode    := piFinEncode
  decode    := piFinDecode
  roundtrip := piFinRoundTrip




noncomputable def encodePreference
    {A : Type} [Fintype A] [DecidableEq A]
    (p : Preference A) : ℕ :=
by
  -- ③ now `inferInstance` succeeds
  haveI : Fintype (A × A) := inferInstance

  -- ④ register the specialised Primcodable instance
  haveI : Primcodable ((A × A) → Bool) :=
    piFintype      -- α resolves to `A × A`, β to `Bool`

  -- ⑤ finally call `encode`
  exact Primcodable.encode
        (fun xy : A × A =>
          if p.rel xy.1 xy.2 then true else false)

noncomputable def decodePreference {A : Type} [Fintype A] [DecidableEq A]
    (n : ℕ) : Option (Preference A) := do
  let b ← Primcodable.decode (α := (A × A) → Bool) n   -- b : A×A → Bool
  -- check `b` really is a strict total order
  if h : IsStrictTotalOrder A (fun x y => b ⟨x, y⟩ = true) then
    pure (Preference.mk (fun x y => b ⟨x, y⟩) h)
  else
    none


theorem roundtripPreference (p : Preference A) :
    decodePreference (encodePreference p) = some p := by
  dsimp [decodePreference, encodePreference]
  -- `Primcodable.decode _ = some b` gives `b = fun (x,y) => decide _`
  -- then `h : IsStrictTotalOrder A (fun x y => decide _)` is definitionally `p.strict_total`
  sorry

noncomputable instance preferencePrimcodable
    {A : Type} [Fintype A] [DecidableEq A] :
    Primcodable (Preference A) where
  encode    := encodePreference
  decode    := decodePreference
  roundtrip := roundtripPreference   -- still a `sorry` for now



end Primcodable

end MyCompute






variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
variable {A : Type} [Fintype A] [DecidableEq A]
variable (hA3 : 3 ≤ Fintype.card A) (hK : 2 ≤ Fintype.card α)

-- now you can write
-- def C (p : Profile α A) : Bool :=
  -- build your classifier in terms of `encode`/`decode` on ℕ
  -- and `Nat.Primrec` to show it's primitive recursive…

-- and prove `C_computable : Computable (C (…))` by unfolding everything
-- into raw `Nat.Primrec` constructors.
