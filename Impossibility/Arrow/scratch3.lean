import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Impossibility.Arrow.ArrowTypes   -- `pref_order` and `lin_pref_order`
import Init.Data.List.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

open Classical

open List
open Classical
open Function
open Fin
open ArrowTypes
open List hiding Vector
open Nat
open List.Perm


universe u
variable {σ : Type u} [Fintype σ] [DecidableEq σ] [BEq σ] [EquivBEq σ]


lemma get_injective_of_nodup
    {α} {l : List α} (hN : l.Nodup) :
    Function.Injective (fun i : Fin l.length => l.get i) := by
  classical
  -- we build a `Pairwise (≠)` witness by simple induction on `Nodup`
  have hPW : List.Pairwise (fun a b : α => a ≠ b) l := by
    induction hN with
    | nil =>
        exact List.Pairwise.nil
    | @cons a l hNotMem hN ih =>
        exact List.Pairwise.cons
          (by
            intro b hb            -- hb : b ∈ l
            intro hEq             -- goal: a ≠ b
            cases hEq             -- now goal: a ≠ a  ≡  False
            exact (hNotMem _ hb) rfl)   -- supply both args to hNotMem, then `rfl`
          ih
  -- turn that `Pairwise` into the “elements at different indices are different” view
  have hNe := (List.pairwise_iff_get
                (R := (fun a b : α => a ≠ b))).1 hPW
  -- wrap up the injectivity proof
  intro i j hij
  by_cases hVal : i.val = j.val
  · exact Fin.ext hVal           -- indices already equal
  · -- otherwise they’re strictly ordered, contradicting `hNe`
    have hlt : i.val < j.val ∨ j.val < i.val :=
      (Nat.lt_or_gt_of_ne hVal)
    cases hlt with
    | inl hlt =>
        have hneq := hNe i j hlt
        exact (hneq hij).elim
    | inr hgt =>
        have hneq := hNe j i hgt
        have hneq' : l.get i ≠ l.get j := by
          intro h; exact hneq h.symm
        exact (hneq' hij).elim



lemma get_at_indexOf
    {α} [DecidableEq α] [BEq α] [EquivBEq α]
    {l : List α} (hN : l.Nodup) {a : α} (ha : a ∈ l) :
    l.get ⟨l.indexOf a, by
             -- bound proof : indexOf a l < l.length
             have := List.indexOf_lt_length ha; simpa using this⟩ = a := by
  classical
  -- Let `i` be that `Fin` index.
  let i : Fin l.length := ⟨l.indexOf a, by
    have := List.indexOf_lt_length ha; simpa using this⟩

  -- `List.get_indexOf` tells us the *index* of `l.get i` is `i`.
  have hIdx : l.indexOf (l.get i) = (i : ℕ) :=
    List.get_indexOf (l := l) hN i

  -- But `(i : ℕ)` is *definitionally* `l.indexOf a` (from the `let`).
  have hIdx' : l.indexOf (l.get i) = l.indexOf a := by
    simpa [i] using hIdx

  -- In a nodup list, equal indices  ⇔  equal elements.
  have hMem : l.get i ∈ l := List.get_mem (l := l) (n := i)
  have : l.get i = a :=
    List.eq_of_indexOf_eq (l := l) hN hMem ha hIdx'

  simpa [i] using this


lemma indexOf_get_nat
    {α} [DecidableEq α] [BEq α] [EquivBEq α]
    {l : List α} (hN : l.Nodup) (i : Fin l.length) :
    l.indexOf (l.get i) = i.val := by
  classical
  ------------------------------------------------------------------
  -- 1 ▸ `l.get i` is in `l`
  ------------------------------------------------------------------
  have hMem : l.get i ∈ l :=
    List.get_mem (l := l) (n := i)

  ------------------------------------------------------------------
  -- 2 ▸ package `indexOf (l.get i)` as a `Fin`
  ------------------------------------------------------------------
  have hLt : l.indexOf (l.get i) < l.length :=
    List.indexOf_lt_length hMem
  let j : Fin l.length := ⟨l.indexOf (l.get i), hLt⟩

  ------------------------------------------------------------------
  -- 3 ▸ the two `Fin`s pick the same element
  ------------------------------------------------------------------
  have hGet : l.get j = l.get i := by
    -- `get_at_indexOf` is the helper lemma you defined earlier
    --     get_at_indexOf hN hMem :
    --       l.get ⟨l.indexOf (l.get i), _⟩ = l.get i
    simpa [j] using get_at_indexOf (l := l) hN hMem

  ------------------------------------------------------------------
  -- 4 ▸ injectivity of `get` on a `Nodup` list  ⇒  `j = i`
  ------------------------------------------------------------------
  have hEqFin : j = i :=
    (get_injective_of_nodup (α := α) (l := l) hN) hGet

  ------------------------------------------------------------------
  -- 5 ▸ extract the numeric equality
  ------------------------------------------------------------------
  simpa [j] using congrArg Fin.val hEqFin



















lemma get_at_indexOf
    {α} [DecidableEq α]          -- the BEq / EquivBEq instances aren’t needed here
    {l : List α}
    (hN : l.Nodup) {a : α} (ha : a ∈ l) :
    l.get ⟨l.indexOf a, List.indexOf_lt_length ha⟩ = a := by
  -- `List.get_indexOf` is exactly the lemma we’re proving
  simpa using List.get_indexOf (l := l) hN ha






/-! 2 ▸ same `indexOf` ⇒ same element (any compatible `BEq`) ---------- -/
lemma List.eq_of_indexOf_eq
    {α : Type _} [DecidableEq α] [BEq α] [EquivBEq α]  -- ← added
    {l : List α} (hN : l.Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hIdx : l.indexOf x = l.indexOf y) : x = y := by
  classical
  ------------------------------------------------------------
  -- 1. read the list at the two canonical indices
  ------------------------------------------------------------
  have hGetx :
      l.get ⟨l.indexOf x, List.indexOf_lt_length hx⟩ = x :=
    get_at_indexOf (l := l) hN hx
  have hGety :
      l.get ⟨l.indexOf y, List.indexOf_lt_length hy⟩ = y :=
    get_at_indexOf (l := l) hN hy

  ------------------------------------------------------------
  -- 2. lift the numeric equality to a `Fin` equality
  ------------------------------------------------------------
  have hFin :
      (⟨l.indexOf x, List.indexOf_lt_length hx⟩ : Fin l.length) =
      ⟨l.indexOf y, List.indexOf_lt_length hy⟩ := by
    apply Fin.ext
    simpa using hIdx

  ------------------------------------------------------------
  -- 3. rewrite and conclude
  ------------------------------------------------------------
  have : l.get ⟨l.indexOf x, List.indexOf_lt_length hx⟩ = y := by
    simpa [hFin] using hGety
  simpa [hGetx] using this
