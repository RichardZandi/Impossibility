import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Partrec
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs
import Impossibility.Arrow.ArrowTypes
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Defs
import Init.Data.List.Lemmas

universe u
variable {σ : Type u} [Fintype σ] [DecidableEq σ] [BEq σ] [EquivBEq σ]

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

open Classical
open Function
open Fin
open ArrowTypes
open List hiding Vector
open Nat
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


/-! 1 ▸ an element read back at its own `indexOf` --------------------- -/
lemma get_at_indexOf
    {α} [DecidableEq α] {l : List α}
    (hN : l.Nodup) {a : α} (ha : a ∈ l) :
    l.get ⟨l.indexOf a, List.indexOf_lt_length ha⟩ = a := by
  -- library lemma once we spell out `l`
  simpa using List.get_indexOf (l := l) hN ha


/-! 2 ▸ same `indexOf` ⇒ same element --------------------------------- -/
lemma List.eq_of_indexOf_eq
    {α : Type _} [DecidableEq α] [BEq α] [EquivBEq α]
    {l : List α} (hN : l.Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hIdx : l.indexOf x = l.indexOf y) : x = y := by
  classical
  ----------------------------------------------------------------
  -- equality provided by the first lemma for each element
  ----------------------------------------------------------------
  have hGetx :
      l.get ⟨l.indexOf x, List.indexOf_lt_length hx⟩ = x :=
    get_at_indexOf (l := l) hN hx

  have hGety :
      l.get ⟨l.indexOf y, List.indexOf_lt_length hy⟩ = y :=
    get_at_indexOf (l := l) hN hy

  ----------------------------------------------------------------
  -- turn the numeric index equality into a `Fin` equality
  ----------------------------------------------------------------
  have hFin :
      (⟨l.indexOf x, List.indexOf_lt_length hx⟩ : Fin l.length) =
      ⟨l.indexOf y, List.indexOf_lt_length hy⟩ := by
    apply Fin.ext
    simpa using hIdx

  ----------------------------------------------------------------
  -- rewrite `hGety` along that equality, then finish
  ----------------------------------------------------------------
  have : l.get ⟨l.indexOf x, List.indexOf_lt_length hx⟩ = y := by
    simpa [hFin] using hGety

  simpa [hGetx] using this


lemma List.eq_of_indexOf_eq1
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


/- THESE HELPER LEMMAS WORK-/
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
#check List.Vector.toList_injective
#check Vector.toList_injective
#check sorted_P_implies_sorted_R
#check List.indexOf
#check Vector.toList
#check List.get           -- expected: (l : List α) → Fin l.length → α
#check List.get_eq_getElem
#check List.pairwise_iff_get
#check List.get_indexOf
#check List.get_eq_getElem   -- Lean shows either  `l.get i = l[↑i]`  or  the reverse
#check (fun (l : List Nat) (i : Fin l.length) ↦ l[i])
#check List.indexOf_lt_length
#check List.Sorted.rel_get_of_lt




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
-- #check Array.toList_injective Dont' Have
-- #check List.rel_get_of_le
-- #check eq_of_toList_eq                  -- the lemma we kept
-- #check _root_.Vector.toList
-- #check List.indexOf_cons_of_ne
-- #check (·[·] : List _ → _ → _)
-- #check pairwise_rel_on_indices
-- #check List.indexOf_eq_some
-- #check List.mem_take
-- #check List.mem_drop
-- #check List.Pairwise.rel_get_of_lt





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

lemma indexOf_get_nat
    {α} [DecidableEq α] {l : List α}
    (hN : l.Nodup) (i : Fin l.length) :
    l.indexOf (l.get i) = i.val := by
  classical

  have hMem : l.get i ∈ l := by
    simpa using List.get_mem (l := l) (n := i)

  have hLt : l.indexOf (l.get i) < l.length :=
    List.indexOf_lt_length hMem

  set j : Fin l.length := ⟨_, hLt⟩ with hjDef   -- so we can rewrite `j.val`

  have hGet : l.get j = l.get i := by
    simpa [hjDef] using List.get_indexOf hMem

  have hEq : j = i :=
    (get_injective_of_nodup (α := α) (l := l) hN) hGet

  simpa [hjDef] using congrArg Fin.val hEq


private lemma Ranking.eq_of_vec_eq {σ} [Fintype σ]
    {r₁ r₂ : Ranking σ} (h : r₁.vec = r₂.vec) : r₁ = r₂ := by
  cases r₁; cases r₂; cases h; rfl

private lemma nodup_refVec {σ} [Fintype σ] :
    (refVec (σ := σ)).toList.Nodup := by
  simp [refVec, Vector.toList_ofFn, List.nodup_ofFn, Function.Injective]

open List

lemma indexOf_lt_len {α} [DecidableEq α] {l : List α} {a : α}
    (h : a ∈ l) : l.indexOf a < l.length :=
  List.indexOf_lt_length h


lemma indexOf_head_or_tail (a x : α) (xs : List α) :
    List.indexOf a (x :: xs) =
      if h : a = x then 0 else List.indexOf a xs + 1 := by
  by_cases h : a = x
  ·           -- head case
    subst h
    simp [List.indexOf]
  ·           -- tail case
    -- Lean also needs `x ≠ a`
    have hxne : x ≠ a := by
      intro hx
      exact h (hx.symm)
    simp [List.indexOf, h, hxne, Nat.succ_eq_add_one]


lemma indexOf_cons_eq_zero (a x : α) (xs : List α) (h : a = x) :
    List.indexOf a (x :: xs) = 0 := by
  simp [indexOf_head_or_tail, h]

lemma indexOf_cons_ne (a x : α) (xs : List α) (h : a ≠ x) :
    List.indexOf a (x :: xs) = List.indexOf a xs + 1 := by
  have hxne : x ≠ a := by
    intro hx; exact h (hx.symm)
  simp [indexOf_head_or_tail, h, hxne]



lemma pairwise_rel_on_indices
    {α} {r : α → α → Prop} {l : List α}
    (h : l.Pairwise r) {i j : Fin l.length} (hij : (i : ℕ) < j) :
    r (l.get i) (l.get j) :=
by
  -- one direction of `pairwise_iff_get`
  have := (pairwise_iff_get).1 h
  simpa using this i j hij

/-- rewrite the bracket form `l[↑i]` into `l.get i` -/
@[simp] lemma bracket_to_get {α}
    (l : List α) (i : Fin l.length) :
    (l[↑i] : α) = l.get i := by
  -- In your build `List.get_eq_getElem` is `l.get i = l[↑i]`,
  -- so we take its symmetric form.
  have := List.get_eq_getElem (l := l) (i := i)
  simpa using this.symm

/-- rewrite `l.get i` back to the bracket form -/
@[simp] lemma get_to_bracket {α} (l : List α) (i : Fin l.length) :
    l.get i = l[↑i] :=
  by
    simp [List.get_eq_getElem]



lemma indexOf_le_indexOf
    {α : Type*} [DecidableEq α]
    {r : α → α → Prop} [IsRefl α r]
    (antisymm : ∀ {x y : α}, r x y → r y x → x = y)
    {l : List α} (hSorted : l.Sorted r) (hNodup : l.Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) :
    l.indexOf a ≤ l.indexOf b ↔ r a b := by
  classical
  refine ⟨?fwd, ?bwd⟩

  ------------------------------------------------------------------ forward →
  · intro hIdx
    -- package the two `indexOf`s as `Fin`s
    have ha_lt : l.indexOf a < l.length := List.indexOf_lt_length ha
    have hb_lt : l.indexOf b < l.length := List.indexOf_lt_length hb
    let ia : Fin l.length := ⟨l.indexOf a, ha_lt⟩
    let ib : Fin l.length := ⟨l.indexOf b, hb_lt⟩

    have hrel : r (l.get ia) (l.get ib) :=
      hSorted.rel_get_of_le (by
        dsimp [ia, ib]; exact hIdx)

    have hgeta : l.get ia = a := by
      simpa [ia] using List.get_indexOf ha
    have hgetb : l.get ib = b := by
      simpa [ib] using List.get_indexOf hb

    have hgeta' : (l[↑ia] : α) = a := by
      simpa [List.get_eq_getElem] using hgeta
    have hgetb' : (l[↑ib] : α) = b := by
      simpa [List.get_eq_getElem] using hgetb

    trace_state
    have h_ab : r a b := by
      have h := hrel                       -- start from r (l.get ia) (l.get ib)
      simp_rw [hgeta, hgetb] at h          -- rewrite both sides using the equalities
      exact h

    exact h_ab

  ------------------------------------------------------------------ backward ←
  · intro hRel
    by_contra hNotLe                         -- introduce the negated goal
    have hLt : l.indexOf b < l.indexOf a :=
      Nat.lt_of_not_ge hNotLe

    -- build `Fin`s again
    have ha_lt : l.indexOf a < l.length := List.indexOf_lt_length ha
    have hb_lt : l.indexOf b < l.length := List.indexOf_lt_length hb
    let ia : Fin l.length := ⟨l.indexOf a, ha_lt⟩
    let ib : Fin l.length := ⟨l.indexOf b, hb_lt⟩

    -- `Sorted` gives the *opposite* relation because indices are flipped
    have hrel' : r (l.get ib) (l.get ia) :=
      hSorted.rel_get_of_lt (by
        dsimp [ia, ib]; exact hLt)

    -- rewrite `get`s back to `a`, `b`
    have hgeta : l.get ia = a := by
      simpa [ia] using List.get_indexOf ha
    have hgetb : l.get ib = b := by
      simpa [ib] using List.get_indexOf hb

    -- rewrite only with those equalities
    have hba : r b a := by
      have h := hrel'
      simp_rw [hgeta, hgetb] at h
      exact h

    -- antisymmetry forces a = b, contradicting strict inequality
    have hEq : a = b := antisymm hRel hba
    have : l.indexOf a < l.indexOf a := by
      simpa [hEq] using hLt
    exact (Nat.lt_irrefl _ this).elim


attribute [ext] lin_pref_order



noncomputable def equivPref : ArrowTypes.lin_pref_order σ ≃ Ranking σ where
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
              have hx : x ∈ r.vec.toList := by
                -- every element is in the canonical reference vector
                have href : x ∈ (refVec (σ := σ)).toList := mem_refVec x
                -- transport membership across the permutation in `r.complete`
                exact (vector_perm_mem_iff r.complete x).mpr href
              have hy : y ∈ r.vec.toList := by
                have href : y ∈ (refVec (σ := σ)).toList := mem_refVec y
                exact (vector_perm_mem_iff r.complete y).mpr href
                            -- indices equal ⇒ elements equal, avoiding the BEq clash
              exact List.eq_of_indexOf_eq r.nodup hx hy hIdx
              }

  left_inv := by
    intro p
    ext a b

    set L : List σ := (encodePref p.topref_order).toList with hL

    have hPermVec := encodePref_perm_ref (σ := σ) (p := p.topref_order)

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

    have hIdx :
        L.indexOf a ≤ L.indexOf b ↔ p.R a b :=
      indexOf_le_indexOf
        (antisymm := by
          intro x y hxy hyx
          exact p.antisymm hxy hyx)
        hSorted hNodup ha hb

    simpa [ofPref, Ranking.toPref, hL] using hIdx


  right_inv := by
    rintro ⟨v, hN, hP⟩                -- any `Ranking σ`
    set w : _root_.Vector σ (Fintype.card σ) :=
      encodePref (toPref ⟨v, hN, hP⟩) with hw

    have hPerm : w.Perm v := by
      -- `w` perm refVec and `v` perm refVec ⇒ `w` perm `v`
      have hwRef : w.Perm (refVec (σ := σ)) :=
        encodePref_perm_ref (σ := σ) (p := toPref ⟨v, hN, hP⟩)
      exact hwRef.trans hP.symm                       -- hP : v perm refVec

    haveI : IsTotal σ (toPref ⟨v, hN, hP⟩).R :=
      ⟨by intro a b; dsimp [toPref]; exact Nat.le_total _ _⟩
    haveI : IsTrans σ (toPref ⟨v, hN, hP⟩).R :=
      ⟨by intro a b c; dsimp [toPref]; exact Nat.le_trans⟩

    have hSorted_w :
        w.toList.Sorted (toPref ⟨v, hN, hP⟩).R := by
      simpa [hw, encodePref] using
        List.sorted_insertionSort
          (l := (refVec (σ := σ)).toList)
          (r := (toPref ⟨v, hN, hP⟩).R)

    have hSorted_v :
        v.toList.Sorted (toPref ⟨v, hN, hP⟩).R := by
      -- prove the Pairwise form directly from indices
      have hPair :
          v.toList.Pairwise (toPref ⟨v, hN, hP⟩).R := by
        -- use `pairwise_iff_get`
        apply (List.pairwise_iff_get).2
        intro i j hlt                        -- i < j
        -- expand the relation: indexOf … ≤ indexOf …
        dsimp [toPref]                           -- expand the relation

        have hi : indexOf (v[↑i]) v.toList = (i : ℕ) := by
          letI : BEq σ := instBEqOfDecidableEq
          -- `bracket_to_get`   :  (l[↑i] : α) = l.get i
          trace_state
          simpa [bracket_to_get] using
            (indexOf_get_nat (l := v.toList) hN i)

        have hj : indexOf (v[↑j]) v.toList = (j : ℕ) := by
          letI : BEq σ := instBEqOfDecidableEq
          simpa [bracket_to_get] using
            (indexOf_get_nat (l := v.toList) hN j)

        -- ❷  numeric inequality coming from  i < j ---------------------
        have hle : (i : ℕ) ≤ j := Nat.le_of_lt hlt

        -- ❸  close the goal -------------------------------------------
        -- after rewriting with `hi` and `hj`, the goal *is* `hle`
        simpa [hi, hj] using hle
      simpa [List.Sorted] using hPair

    have h_asymm :
        ∀ {a b : σ},
          (toPref ⟨v, hN, hP⟩).R a b →
          (toPref ⟨v, hN, hP⟩).R b a →
          a = b := by
      intro a b hab hba
      dsimp [toPref] at hab hba
      exact Nat.le_antisymm hab hba

    have hEqList : v.toList = w.toList := by
      have hPermList : v.toList.Perm w.toList :=
        (Vector.perm_iff_toList_perm).1 hPerm
      exact List.sorted_perm_eq
              hSorted_v hSorted_w hPermList h_asymm

    have hEqVec : w = v := by
      -- `Vector.toList` is injective
      apply (Vector.toList_injective (α := σ))
      simpa using hEqList.symm               -- orientation for `w = v`

    have : ofPref (toPref ⟨v, hN, hP⟩) =
        (⟨v, hN, hP⟩ : Ranking σ) := by
      apply Ranking.eq_of_vec_eq
      simpa [ofPref, hw] using hEqVec

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
