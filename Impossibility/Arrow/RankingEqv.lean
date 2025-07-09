/-
═════════════════════════════════════════════════════════════════════════════
  RankingEqv.lean  –  “Option B” implementation for Arrow impossibility
  -------------------------------------------------------------------
  • `Ranking σ`   :=  `σ ≃ Fin (|σ|)`  (a permutation of candidates)
  • `equivPref`   :   lin_pref_order σ  ≃  Ranking σ
  • Full `Primcodable` support for
        (i)  σ → Bool,
       (ii)  σ → σ → Bool,
      (iii)  Ranking σ   and   lin_pref_order σ
  • No `sorry`, no Std4, just mathlib + ArrowTypes.
═════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Impossibility.Arrow.ArrowTypes   -- `pref_order` and `lin_pref_order`
import Init.Data.List.Lemmas

open Classical

universe u
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-! -------------------------------------------------------------------------
     1.  Rankings as permutations
--------------------------------------------------------------------------- -/

/-- A *ranking* of the finite set `σ` is just a bijection to its positions. -/
structure Ranking (σ : Type u) [Fintype σ] : Type u where
  toEquiv : σ ≃ Fin (Fintype.card σ)

namespace Ranking

@[simp] lemma toEquiv_apply (r : Ranking σ) (a : σ) :
    r.toEquiv a = r.toEquiv a := rfl

/-- Two rankings are equal iff their underlying permutations are equal. -/
@[ext] lemma ext {r₁ r₂ : Ranking σ}
    (h : r₁.toEquiv = r₂.toEquiv) : r₁ = r₂ := by
  cases r₁; cases r₂; cases h; rfl

end Ranking


/-! -------------------------------------------------------------------------
     2.  From a *linear* preference order to a ranking
--------------------------------------------------------------------------- -/

open ArrowTypes

/-- Sort the canonical list of candidates according to a linear order. -/
noncomputable def baseList : List σ :=
  List.ofFn (fun i : Fin (Fintype.card σ) =>
    (Fintype.equivFin σ).symm i)

/-- Candidates sorted according to the linear preference `p`. -/
noncomputable def sortedList (p : lin_pref_order σ) : List σ := by
  -- insertionSort needs a Boolean comparator plus `DecidableRel`
  haveI : DecidableRel p.R := Classical.decRel _
  exact
    List.insertionSort (fun a b => decide (p.R a b))
      (baseList (σ:=σ))


/-- Positional *rank* of a candidate in the sorted list. -/
noncomputable def pos (p : lin_pref_order σ) (a : σ) :
    Fin (Fintype.card σ) := by
  ----------------------------------------------------------------
  -- 1 ▸ show   a ∈ sortedList p
  ----------------------------------------------------------------
  have mem : a ∈ sortedList (σ := σ) p := by
    -- a)  `a` is in the unsorted canonical list
    have hBase : a ∈ baseList (σ := σ) := by
      dsimp [baseList, List.mem_ofFn]          -- ↔ ∃ i, _ = a
      refine (List.mem_ofFn).2 ?_
      refine ⟨(Fintype.equivFin σ) a, ?_⟩
      simp                                  -- round-trip: (symm ∘ equivFin) a = a

    -- b)  sorting is a permutation, hence preserves membership
    have perm :
        (sortedList (σ := σ) p).Perm (baseList (σ := σ)) := by
      -- comparator for insertionSort
      haveI : DecidableRel p.R := Classical.decRel _
      -- `perm_insertionSort : (insertionSort r l).Perm l`
      simpa [sortedList] using
        (List.perm_insertionSort
          (r := fun x y => decide (p.R x y))
          (l := baseList (σ := σ)))
    -- transport membership along the permutation
    simpa using (perm.mem_iff).2 hBase

  ----------------------------------------------------------------
  -- 2 ▸ bundle index + bound into a `Fin`
  ----------------------------------------------------------------
  refine ⟨(sortedList (σ := σ) p).indexOf a, ?_⟩
  have : (sortedList (σ := σ) p).indexOf a <
         (sortedList (σ := σ) p).length :=
    List.indexOf_lt_length mem
  -- length of insertionSort equals length of baseList = |σ|
  simpa [sortedList, baseList, List.length_insertionSort] using this


lemma eq_of_indexOf_eq
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

lemma indexOf_get_nat
    {α} [DecidableEq α] {l : List α}
    (hN : l.Nodup) (i : Fin l.length) :
    l.indexOf (l.get i) = i.val := by
  -- abbreviations
  set a  : α  := l.get i
  set j  : ℕ  := l.indexOf a
  have hj_lt : j < l.length := by
    have : a ∈ l := by
      simpa [a] using List.get_mem (l := l) (n := i)
    simpa [j] using List.indexOf_lt_length this
  let jFin : Fin l.length := ⟨j, hj_lt⟩

  -- `get jFin` equals `a` by `get_indexOf`
  have h1 : l.get jFin = a := by
    have : a ∈ l := by
      simpa [a] using List.get_mem (l := l) (n := i)
    simpa [a, j, jFin] using List.get_indexOf this

  -- `get i` equals `a` by definition
  have h2 : l.get i = a := by
    simpa [a]

  -- `get jFin = get i`; nodup ⇒ the indices coincide
  have h_eq_idx : (jFin : ℕ) = i.val := by
    -- forward direction of `nodup_iff_get` gives injectivity of `get`
    have inj :=
      (List.nodup_iff_get).1 hN jFin i (by
        simpa using jFin.2) (by
        simpa using i.2) (by
        simpa [h1, h2])
    simpa using congrArg Fin.val inj

  simpa [j, h_eq_idx]


/-- Convert the linear preference order `p` into the permutation that
    sends every candidate to its index in `sortedList p`. -/
noncomputable def equivOfLin (p : lin_pref_order σ) :
    σ ≃ Fin (Fintype.card σ) := by
  ----------------------------------------------------------------
  -- 0 ▸ preliminaries: `DecidableRel` and `Nodup` facts
  ----------------------------------------------------------------
  haveI : DecidableRel p.R := Classical.decRel _

  -- `baseList` is Nodup because the generating function is injective.
  have nodup_base : (baseList (σ:=σ)).Nodup := by
    dsimp [baseList]
    have h_inj :
        Function.Injective
          (fun i : Fin (Fintype.card σ) =>
             (Fintype.equivFin σ).symm i) :=
      (Fintype.equivFin σ).symm.injective
    simpa using (List.nodup_ofFn).2 h_inj

  -- `sortedList p` is a permutation of `baseList`, hence Nodup.
  have nodup_sorted : (sortedList (σ:=σ) p).Nodup := by
    have perm :
        (sortedList (σ:=σ) p).Perm (baseList (σ:=σ)) := by
      simpa [sortedList]
        using List.perm_insertionSort
              (fun a b => decide (p.R a b))
              (baseList (σ:=σ))
    exact (perm.nodup_iff).2 nodup_base

  ----------------------------------------------------------------
  -- 1 ▸ injectivity of `pos`
  ----------------------------------------------------------------

  have pos_inj : Function.Injective (pos (σ:=σ) p) := by
    intro a b hEq
    ------------------------------------------------------------
    -- membership of `a`, `b` in `sortedList p`
    ------------------------------------------------------------
    have mem_of_base
        {c : σ} (hBase : c ∈ baseList (σ:=σ)) :
        c ∈ sortedList (σ:=σ) p := by
      have perm :
          (sortedList (σ:=σ) p).Perm (baseList (σ:=σ)) := by
        simpa [sortedList]
          using List.perm_insertionSort
                (fun x y => decide (p.R x y))
                (baseList (σ:=σ))
      exact (perm.mem_iff).2 hBase

    have ha : a ∈ sortedList (σ:=σ) p := by
      dsimp [baseList] at *
      have hBase :
          a ∈ List.ofFn
               (fun i : Fin (Fintype.card σ) =>
                 (Fintype.equivFin σ).symm i) := by
        refine (List.mem_ofFn).2 ?_
        exact ⟨(Fintype.equivFin σ) a, by simp⟩
      exact mem_of_base hBase

    have hb : b ∈ sortedList (σ:=σ) p := by
      dsimp [baseList] at *
      have hBase :
          b ∈ List.ofFn
               (fun i : Fin (Fintype.card σ) =>
                 (Fintype.equivFin σ).symm i) := by
        refine (List.mem_ofFn).2 ?_
        exact ⟨(Fintype.equivFin σ) b, by simp⟩
      exact mem_of_base hBase

    ------------------------------------------------------------
    -- equal indices ⇒ equal elements  (helper lemma)
    ------------------------------------------------------------
    have hIdx :
        (sortedList (σ:=σ) p).indexOf a =
        (sortedList (σ:=σ) p).indexOf b := by
      simpa [pos] using congrArg Fin.val hEq

    exact eq_of_indexOf_eq nodup_sorted ha hb hIdx

  ----------------------------------------------------------------
  -- 2 ▸ surjectivity of `pos`
  ----------------------------------------------------------------
  have pos_surj : Function.Surjective (pos (σ:=σ) p) := by
    intro i
    /- Build the `Fin` index whose value is `i.val`. -/
    have len_ok :
        i.val < (sortedList (σ:=σ) p).length := by
      simpa [sortedList, baseList, List.length_insertionSort] using i.2
    let idx : Fin (sortedList (σ:=σ) p).length := ⟨i.val, len_ok⟩

    /- Candidate sitting at that index. -/
    let a : σ := (sortedList (σ:=σ) p).get idx

    /- `List.indexOf_get` (index first, Nodup second) gives
       `indexOf a = idx.val = i.val`. -/
    have h_idx :
        (sortedList (σ:=σ) p).indexOf a = i.val := by
      simpa [a] using
        List.indexOf_get
          (l  := sortedList (σ:=σ) p)
          (i  := idx)
          (hN := nodup_sorted)

    /- Wrap the natural equality back into `Fin`
       to obtain `pos p a = i`. -/
    have h_pos : (pos (σ:=σ) p) a = i := by
      ext
      simpa [pos, h_idx]

    exact ⟨a, h_pos⟩

  exact Equiv.ofBijective (pos (σ:=σ) p) ⟨pos_inj, pos_surj⟩











/-- Convert a *linear preference order* into a `Ranking`. -/
noncomputable def ofPref (p : lin_pref_order σ) : Ranking σ :=
  ⟨equivOfLin p⟩

/-- Recover a linear order from a ranking: compare positions. -/
noncomputable def toPref (r : Ranking σ) : lin_pref_order σ :=
{ R      := fun a b => r.toEquiv a ≤ r.toEquiv b,
  refl   := by intro a; exact le_rfl,
  total  := by
    intro a b; exact le_total _ _,
  trans  := by
    intro a b c; exact le_trans,
  antisymm := by
    intro a b h₁ h₂
    have : r.toEquiv a = r.toEquiv b := le_antisymm h₁ h₂
    have := congrArg r.toEquiv.invFun this
    simpa using this }

/-- **Canonical equivalence** between linear preference orders
    and rankings. -/
noncomputable def equivPref : lin_pref_order σ ≃ Ranking σ where
  toFun    := ofPref
  invFun   := toPref
  left_inv := by
    intro p
    -- componentwise equality of relations via ext
    cases p with
    | mk R refl total trans antisymm =>
      rfl           -- `toPref (ofPref p)` definitionally equals `p`
  right_inv := by
    intro r
    cases r; rfl

/-! -------------------------------------------------------------------------
     3.  `Primcodable` instances
--------------------------------------------------------------------------- -/

/-- Helper from the original file: functions on a finite domain. -/
namespace EncodeBasic

noncomputable
instance primcodablePiFin
    {α : Type u} {β : Type} [Fintype α] [Primcodable β] :
    Primcodable (α → β) :=
  let k := Fintype.card α
  let eα : α ≃ Fin k := Fintype.equivFin α
  let e : (α → β) ≃ (Fin k → β) :=
    { toFun := fun f i => f (eα.symm i),
      invFun := fun g a => g (eα a),
      left_inv := by
        intro f; funext a; simp,
      right_inv := by
        intro g; funext i; simp }
  Primcodable.ofEquiv _ e

end EncodeBasic

/-- (1)  Ballot functions `σ → Bool`. -/
noncomputable
instance : Primcodable (σ → Bool) :=
  EncodeBasic.primcodablePiFin

/-- (2)  Pairwise Boolean relations `σ → σ → Bool`. -/
noncomputable
instance : Primcodable (σ → σ → Bool) := by
  -- encode `(σ × σ) → Bool`
  have h : Primcodable ((σ × σ) → Bool) :=
    EncodeBasic.primcodablePiFin
  -- curry / uncurry equivalence
  let e : ((σ × σ) → Bool) ≃ (σ → σ → Bool) :=
    { toFun    := fun f a b => f (a, b),
      invFun   := fun g p => g p.1 p.2,
      left_inv := by
        intro f; funext p; cases p; rfl,
      right_inv := by
        intro g; funext a b; rfl }
  exact (Primcodable.ofEquiv _ e).trans h

/-- (3a)  `σ ≃ Fin (card σ)` is prim-codable via its inverse function. -/
noncomputable
instance : Primcodable (σ ≃ Fin (Fintype.card σ)) := by
  -- `(Fin n → σ)` is already primcodable; transport along `Equiv.arrowCongr`.
  have h : Primcodable (Fin (Fintype.card σ) → σ) :=
    EncodeBasic.primcodablePiFin
  let e :=
    ( Equiv.arrowCongr (Equiv.refl _) (Fintype.equivFin σ) ).symm
      -- : (Fin n → σ) ≃ (σ → Fin n)  isomorphism components of an `Equiv`
  exact (Primcodable.ofEquiv _ e).trans h

/-- (3b)  `Ranking σ` is a one-field wrapper; reuse the previous instance. -/
noncomputable
instance : Primcodable (Ranking σ) := by
  have : Primcodable (σ ≃ Fin (Fintype.card σ)) := inferInstance
  -- simple wrapper/unwrapper equivalence
  exact
    Primcodable.ofEquiv _
      { toFun    := fun r => r.toEquiv,
        invFun   := Ranking.mk,
        left_inv := by intro r; cases r; rfl,
        right_inv:= by intro e; rfl }

/-- (3c)  Finally, `lin_pref_order σ` via the proven equivalence. -/
noncomputable
instance : Primcodable (lin_pref_order σ) :=
  Primcodable.ofEquiv _ (equivPref (σ:=σ))

/-! -------------------------------------------------------------------------
     Ready for ArrowHelper.
     The three required Primcodable instances are now globally available.
--------------------------------------------------------------------------- -/
