import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Partrec
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Impossibility.Arrow.ArrowTypes
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Defs

universe u
variable {σ : Type u} [Fintype σ] [DecidableEq σ] [BEq σ]


namespace EncodeBasic

noncomputable
instance primcodablePiFin
    {α : Type u} {β : Type u} [Fintype α] [Primcodable β] :
    Primcodable (α → β) :=
  let k : ℕ := Fintype.card α
  let eα : α ≃ Fin k := Fintype.equivFin α
  let e : (α → β) ≃ (Fin k → β) :=
    { toFun   := fun f i => f (eα.symm i)
    , invFun  := fun g a => g (eα a)
    , left_inv  := by
        intro f; funext a; simp [eα.symm_apply_apply]
    , right_inv := by
        intro g; funext i; simp [eα.apply_symm_apply] }
  Primcodable.ofEquiv _ e

end EncodeBasic


open Fin
open ArrowTypes
open List
open Classical
open Vector
open List Nat
open List.Perm


/-! ### 1  Canonical reference vector ----------------------------------- -/

/-- `0,1,…,card σ − 1` as a vector (no lists in the API). -/
noncomputable def refVec : _root_.Vector σ (Fintype.card σ) :=
  Vector.ofFn (fun i ↦ (Fintype.equivFin σ).symm i)

/-! ### 2  Ranking record (vector-only fields) -------------------------- -/



structure Ranking (σ : Type u) [Fintype σ] [DecidableEq σ] [BEq σ] : Type u where
  vec      : _root_.Vector σ (Fintype.card σ)
  nodup    : vec.toList.Nodup
  complete : vec.Perm (refVec (σ := σ))

namespace Ranking

/-! ### 3  Encode / decode --------------------------------------------- -/

/-- encode a preference as a canonicalised permutation vector -/
noncomputable def encodePref (p : pref_order σ) :
    _root_.Vector σ (Fintype.card σ) := by
  let base : List σ := (refVec (σ := σ)).toList
  let r    : σ → σ → Prop := p.R
  haveI   : DecidableRel r := Classical.decRel _
  let sorted : List σ := base.insertionSort r
  have hlen : sorted.length = Fintype.card σ := by
    have h₁ : sorted.length = base.length :=
      List.length_insertionSort (r := r) (l := base)
    have h₂ : base.length = Fintype.card σ := by
      simpa [base, refVec, Vector.toList_ofFn,
             List.length_map, List.length_finRange] using rfl
    simpa [h₁, h₂]
  let A : Array σ := sorted.toArray
  have hsize : A.size = Fintype.card σ := by
    dsimp [A]; simpa [hlen]
  exact ⟨A, hsize⟩

private lemma encodePref_perm_ref (p : pref_order σ) :
    (encodePref (σ := σ) p).Perm (refVec (σ := σ)) := by
  have hList :
      (encodePref (σ := σ) p).toList ~ (refVec (σ := σ)).toList := by
    simpa [encodePref, refVec, List.toList_toArray]
      using List.perm_insertionSort
            (r := p.R) ((refVec (σ := σ)).toList)
  simpa using (Vector.perm_iff_toList_perm).2 hList


/-- convert a `Ranking` back to a `pref_order`. -/
def toPref (r : Ranking σ) : pref_order σ :=
{ R      := fun a b ↦
    (r.vec.toList.indexOf a) ≤ (r.vec.toList.indexOf b),
  refl   := by intro a; simp,
  total  := by intro a b; exact (Nat.le_total _ _),
  trans  := by intro a b c; exact Nat.le_trans }

/-! ### 4  Packaging the equivalence ----------------------------------- -/

noncomputable def ofPref (p : pref_order σ) : Ranking σ := by
  let v : _root_.Vector σ (Fintype.card σ) := encodePref p

  have perm : v.Perm (refVec (σ := σ)) :=
    encodePref_perm_ref (σ := σ) p

  have nodupOfFn :
      (List.ofFn (fun i : Fin (Fintype.card σ) =>
        (Fintype.equivFin σ).symm i)).Nodup :=
    (List.nodup_ofFn
      (f := fun i : Fin (Fintype.card σ) =>
               (Fintype.equivFin σ).symm i)
    ).mpr
      ((Fintype.equivFin σ).symm.injective)

  have nodupRef : (refVec (σ := σ)).toList.Nodup := by
    simpa [refVec, Vector.toList_ofFn] using nodupOfFn

  have nodup : v.toList.Nodup := by
    have permList := (Vector.perm_iff_toList_perm).1 perm
    exact (permList.nodup_iff).mpr nodupRef

  exact ⟨v, nodup, perm⟩

attribute [ext] pref_order

inductive Name where
  | Alice | Bob | Carl | Dawn | Emma
deriving DecidableEq, Repr, BEq

open Name

def rank : Name → Nat
  | .Alice => 0 | .Bob => 1 | .Carl => 2 | .Dawn => 3 | .Emma => 4

def alphaOrder (a b : Name) : Prop := rank a ≤ rank b

def l : List Name := [Alice, Bob, Carl, Dawn, Emma]

-- 4.  `l` is sorted by `alphaOrder`
lemma l_sorted : l.Sorted alphaOrder := by
  simp [l, alphaOrder, rank, List.Sorted, List.Pairwise]      -- succeeds



lemma List.eq_of_indexOf_eq
    {α : Type _} [DecidableEq α]
    {l : List α} (hN : l.Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hIdx : l.indexOf x = l.indexOf y) : x = y := by
  classical
  -- same index ⇒ same position in the `Fin` view
  have hxFin : l.indexOf x < l.length := by
    simpa using List.indexOf_lt_length (a := x) (l := l) hx
  have hyFin : l.indexOf y < l.length := by
    simpa [hIdx] using List.indexOf_lt_length (a := y) (l := l) hy
  have hxGet : l.get ⟨l.indexOf x, hxFin⟩ = x := by
    simpa using List.get_indexOf hx
  have hyGet : l.get ⟨l.indexOf y, hyFin⟩ = y := by
    simpa [hIdx] using List.get_indexOf hy
  have : l.get ⟨l.indexOf x, hxFin⟩ = y := by
    simpa [hIdx] using hyGet
  simpa [hxGet] using this


lemma mem_refVec {σ} [Fintype σ] (a : σ) :
    a ∈ (refVec (σ := σ)).toList := by
  dsimp [refVec, Vector.toList_ofFn]
  let f : Fin (Fintype.card σ) → σ :=
    fun i ↦ (Fintype.equivFin σ).symm i
  have : a ∈ List.ofFn f := by
    have : f (Fintype.equivFin σ a) = a := by simp [f]
    simpa [List.mem_ofFn, f] using ⟨_, this⟩
  simpa [f]

/-- Transport “membership” across a `Vector` permutation. -/
lemma vector_perm_mem_iff {α n} {v w : _root_.Vector α n}
    (h : _root_.Vector.Perm v w) (a : α) :
    (a ∈ v.toList) ↔ (a ∈ w.toList) := by
  -- mathlib4 already provides the conversion:
  -- (Vector.perm_iff_toList_perm).1 h : List.Perm v.toList w.toList
  have hList : List.Perm v.toList w.toList :=
    (Vector.perm_iff_toList_perm).1 h
  simpa using hList.mem_iff

lemma mem_of_complete {σ} [Fintype σ] (r : Ranking σ) (a : σ) :
    a ∈ r.vec.toList := by
  -- `a` certainly appears in the canonical reference list
  have href : a ∈ (refVec (σ := σ)).toList := mem_refVec a
  -- transport that fact across the permutation stored in `r.complete`
  exact (vector_perm_mem_iff r.complete a).mpr href

private lemma Sorted.imp {α} {r s : α → α → Prop}
    {l : List α} (h : Sorted r l)
    (hmono : ∀ a b, r a b → s a b) :
    Sorted s l := by
  -- `Sorted r l` is exactly `Pairwise r l`:
  --   `Sorted r l`  ↔  `Pairwise r l`
  have : Pairwise r l := h
  have : Pairwise s l := this.imp (by
    intro a b h₁; exact hmono _ _ h₁)
  simpa [Sorted] using this



private lemma sorted_P_implies_sorted_R
    {p : lin_pref_order σ} {l : List σ}
    (h : Sorted (fun a b ↦ P (p : pref_order σ) a b) l) :
    Sorted p.R l :=
  Sorted.imp h (by
    intro a b hP; exact hP.1)


/- THESE HELPER LEMMAS WORKS-/
#check sorted_P_implies_sorted_R
#check Sorted.imp
#check mem_of_complete
#check vector_perm_mem_iff
#check mem_refVec
#check List.eq_of_indexOf_eq

/-THESE WORK-/
#check List.get_idxOf
#check List.Sorted.nodup
#check List.Sorted.cons
#check List.Pairwise.cons
#check List.get_idxOf
#check List.pairwise_iff_get
#check List.indexOf_lt_length
#check List.get_indexOf

/-THESE DO NOT WORK-/
-- #check List.idxOf_eq_some
-- #check List.idxOf_lt_length
-- #check List.mem_take_iff
-- #check List.mem_drop_iff
-- #check List.nthLe_idxOf
-- #check List.nthLe_get
-- #check List.idxOf_le_idxOf
-- #check List.idxOf_lt_idxOf
-- #check List.idxOf_monotone
-- #check List.Sorted.rel_nthLe_of_lt
-- #check List.Pairwise.rel_nthLe_of_lt,
-- #check List.nthLe
-- #check List.nthLe_mem
-- #check List.nthLe_length
-- #check List.nthLe_take
-- #check List.indexOf_eq_some
-- #check List.indexOf_le_indexOf
-- #check List.indexOf_lt_indexOf
-- #check List.indexOf_monotone
-- #check List.get_take
-- #check List.mem_take
-- #check List.mem_drop
-- #check List.Sorted.rel_nthLe_of_lt
-- #check List.Pairwise.rel_nthLe_of_lt


set_option diagnostics true

private lemma List.sorted_perm_eq {α} {r : α → α → Prop}
    {l₁ l₂ : List α}
    (h₁ : l₁.Sorted r) (h₂ : l₂.Sorted r) (hp : l₁.Perm l₂)
    (h_asymm : ∀ {a b}, r a b → r b a → a = b) :
    l₁ = l₂ := by
  -- `Sorted` is definalias for `Pairwise` (see `List.Sorted.eq_1`)
  have h₁pw : l₁.Pairwise r := by
    simpa [List.Sorted.eq_1] using h₁
  have h₂pw : l₂.Pairwise r := by
    simpa [List.Sorted.eq_1] using h₂
  exact List.Perm.eq_of_sorted
        (by
          intro a b ha hb h1 h2; exact h_asymm h1 h2)
        h₁pw h₂pw hp

private lemma Vector.perm_eq_of_sorted
    {α n} {r : α → α → Prop}
    {w v : _root_.Vector α n}
    (hw : w.toList.Sorted r)
    (hv : v.toList.Sorted r)
    (hperm : w.Perm v)
    (h_asymm : ∀ {a b}, r a b → r b a → a = b) :
    w = v := by
  -- lists equal
  have hpermL : w.toList.Perm v.toList :=
    (Vector.perm_iff_toList_perm).1 hperm
  have hEqLists : w.toList = v.toList :=
    List.sorted_perm_eq hw hv hpermL h_asymm

  -- component-wise equality with `List.get?`
  apply Vector.ext
  intro i hi               -- `i : ℕ`, `hi : i < n`

  -- Build a `Fin n` from `(i, hi)`
  let k : Fin n := ⟨i, hi⟩

  -- Transport list equality to element equality
  have hget : w.toList.get k = v.toList.get k := by
    simpa using congrArg (fun l : List α => l.get k) hEqLists

  -- `Vector.get` is definitionally `List.get` on `toList`
  simpa [Vector.get] using hget



private lemma Ranking.eq_of_vec_eq {σ} [Fintype σ]
    {r₁ r₂ : Ranking σ} (h : r₁.vec = r₂.vec) : r₁ = r₂ := by
  cases r₁; cases r₂; cases h; rfl

private lemma nodup_refVec {σ} [Fintype σ] :
    (refVec (σ := σ)).toList.Nodup := by
  simp [refVec, Vector.toList_ofFn, List.nodup_ofFn, Function.Injective]


lemma indexOf_le_indexOf
    {α : Type*} [DecidableEq α] {r : α → α → Prop}
    (antisymm : ∀ {x y : α}, r x y → r y x → x = y)
    {l : List α} (hSorted : l.Sorted r) (hNodup : l.Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) :
    l.indexOf a ≤ l.indexOf b ↔ r a b := by
  -- proof to be filled in later
  sorry



attribute [ext] lin_pref_order

noncomputable def equivPref
  {σ : Type u} [Fintype σ] [DecidableEq σ] [BEq σ] :
    ArrowTypes.lin_pref_order σ ≃ Ranking σ :=
sorry


noncomputable def equivPrefz : ArrowTypes.lin_pref_order σ ≃ Ranking σ where
  toFun   := fun p => ofPref (p : pref_order σ)

  invFun := fun r =>
    by
      -- recover the underlying weak order from the `Ranking`
      let pr : pref_order σ := toPref r
      -- build the linear preference order, supplying antisymmetry
      exact
        { R      := pr.R
          , refl  := pr.refl
          , total := pr.total
          , trans := pr.trans
          , antisymm := by
              intro x y hxy hyx                    -- x ≤ y ≤ x
              -- same position in the ranking vector ⇒ equal elements
              have hIdx :
                  (r.vec.toList).indexOf x = (r.vec.toList).indexOf y :=
                Nat.le_antisymm hxy hyx
              have hx : x ∈ r.vec.toList := mem_of_complete r x
              have hy : y ∈ r.vec.toList := mem_of_complete r y
              exact List.eq_of_indexOf_eq r.nodup hx hy hIdx }

  left_inv := by
    intro p
    ext a b
    set L : List σ := (encodePref (p : pref_order σ)).toList with hL
    have hPermVec := encodePref_perm_ref (p : pref_order σ) (σ := σ)
    have ha : a ∈ L := by
      have : a ∈ (refVec (σ := σ)).toList := mem_refVec a
      simpa [hL] using (vector_perm_mem_iff hPermVec a).2 this
    have hb : b ∈ L := by
      have : b ∈ (refVec (σ := σ)).toList := mem_refVec b
      simpa [hL] using (vector_perm_mem_iff hPermVec b).2 this
    have hSorted : L.Sorted p.R := by
      simpa [hL, encodePref] using
        List.sorted_insertionSort
          (l := (refVec (σ := σ)).toList)
          (r := p.R)
    have hNodup : L.Nodup := by
      have hPermList : List.Perm L (refVec (σ := σ)).toList :=
        (Vector.perm_iff_toList_perm).1 hPermVec
      exact (hPermList.nodup_iff).mpr nodup_refVec
    have hIdx :=
      indexOf_le_indexOf
        (antisymm := by
          intro x y hxy hyx; exact p.antisymm hxy hyx)
        hSorted hNodup ha hb
    simpa [hL] using hIdx

  right_inv := by
    rintro ⟨v, hN, hP⟩
    -- w := canonical list produced by encodePref
    set w := encodePref (toPref ⟨v, hN, hP⟩) with hw

    -- w is a permutation of v
    have hPerm : w.Perm v := by
      have hwRef : w.Perm (refVec (σ := σ)) :=
        encodePref_perm_ref (toPref ⟨v, hN, hP⟩)
      exact hwRef.trans hP.symm

    -- both lists are sorted by the preference relation p.R
    have hSorted_w : w.toList.Sorted (toPref ⟨v, hN, hP⟩).R :=
      by
        -- `encodePref` is insertion-sort
        simpa [encodePref] using
          List.sorted_insertionSort
            (l := (refVec (σ := σ)).toList)
            (r := (toPref ⟨v, hN, hP⟩).R)
    have hSorted_v : v.toList.Sorted (toPref ⟨v, hN, hP⟩).R := by
      -- the `Ranking` invariant gives completeness → permutation with refVec,
      -- hence same order as w
      have : v.Perm (refVec (σ := σ)) := hP
      have : v.toList = w.toList := by
        exact List.Perm.eq_of_perm_of_sorted hPerm hSorted_w (by
          -- refVec is sorted by construction
          simpa [refVec] using this)
      simpa [this] using hSorted_w

    -- permutation + same Sorted order ⇒ equality
    have hEqVec : w = v :=
      Vector.ext fun i =>
        (List.Perm.eq_of_perm_of_sorted hPerm hSorted_w hSorted_v).symm ▸ rfl

    have : ofPref (toPref ⟨v, hN, hP⟩) = (⟨v, hN, hP⟩ : Ranking σ) := by
      apply Ranking.eq_of_vec_eq
      simpa [ofPref, hw, hEqVec]

    simpa using this




end Ranking

/-! ### 5  Computable instances ---------------------------------------- -/


noncomputable instance PrimcodableBool : Primcodable Bool :=
  inferInstance


noncomputable instance PrimcodablePiBool
  {α : Type} [Fintype α] [DecidableEq α] [BEq α] :
  Primcodable (α → Bool) :=
  @EncodeBasic.primcodablePiFin α Bool _ PrimcodableBool


noncomputable instance PrimcodablePiProp
  {α : Type} [Fintype α] [DecidableEq α] [BEq α] :
  Primcodable (α → α → Prop) :=
  Primcodable.ofEquiv (α → α → Bool)
  { toFun := fun f a b => decide (f a b),
    invFun := fun f a b => f a b = true,
    left_inv := by
      intros f; funext a b
      dsimp; simp [decide_eq_true_eq],
    right_inv := by
      intros f; funext a b
      dsimp; simp [decide_eq_true_eq] }

noncomputable instance RankingPrimcodable
  {α : Type} [Fintype α] [DecidableEq α] [BEq α]
  [Primcodable (α → α → Prop)] :
  Primcodable (Ranking α) :=
Primcodable.ofEquiv _ (Equiv.symm Ranking.equivPref)

noncomputable instance linPrefOrderPrimcodable
  {α : Type} [Fintype α] [DecidableEq α] [BEq α]
  [Primcodable (α → α → Prop)] :
  Primcodable (lin_pref_order α) :=
Primcodable.ofEquiv _ Ranking.equivPref
