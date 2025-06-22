import Mathlib.Data.Fintype.Basic        -- Fintype, Fin n
import Mathlib.Algebra.Order.Ring.Nat    -- ℕ, Nat.sqrt for unpair
import Mathlib.Data.Finset.Basic   -- for `Finset.toList`
import Mathlib.Tactic.FinCases   -- for `fin_cases`
import Mathlib.Data.Fintype.Prod   -- ← NEW
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.DeriveFintype   -- provides the handler
import Mathlib.Tactic

/-! ### A minimal “Primcodable” library from scratch -/


open List         -- for unfoldr? and List.foldl
open Finset       -- for `toList`
open Classical
open Nat
open Option

/-- A minimal `Primcodable` for demonstration purposes. -/
class Primcodable (α : Type) where
  encode : α → ℕ
  decode : ℕ → Option α
  roundtrip : ∀ x, decode (encode x) = some x

namespace Primcodable
instance : Primcodable Bool where
  encode | true  => 1 | false => 0
  decode | 1 => some true | 0 => some false | _ => none
  roundtrip b := by cases b <;> rfl
end Primcodable
open Primcodable

open List

variable {α β : Type} [Fintype α] [Primcodable β]

private def peel {β} [Primcodable β] :
    ℕ → ℕ → List β → Option (List β)
  | _, 0,     acc => some acc
  | n, k+1,   acc => do
      let (m,n') := unpair n
      let b ← Primcodable.decode m
      peel n' k (b :: acc)
termination_by _ k _ => k

noncomputable
def enc (f : α → β) : ℕ :=
  let k := Fintype.card α
  (finRange k).foldr
    (fun (i : Fin k) acc =>
      pair (encode (f ((Fintype.equivFin α).symm i))) acc) 0

noncomputable
def dec (n : ℕ) : Option (α → β) := by
  let k := Fintype.card α
  match peel n k ([] : List β) with
  | none     => exact none
  | some rs  =>
      let bs := rs.reverse
      if h : bs.length = k then
        let g : α → β := fun a =>
          let i : Fin k := (Fintype.equivFin α) a
          bs.get ⟨i, by simpa [h] using i.isLt⟩
        exact some g
      else exact none

lemma roundtrip (f : α → β) : dec (enc f) = some f := by
  -- one `simp` is enough once BOTH sides use the same order
  simp [enc, dec,
        peel,           -- unfolds once, reduces to the happy branch
        unpair_pair,
        Primcodable.roundtrip,
        List.foldr,
        List.length_map,
        List.length_reverse,
        List.length_finRange,
        Equiv.symm_apply_apply]  -- closes by definition
