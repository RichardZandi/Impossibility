/-
Impossibility/Arrow/ArrowTypes.lean
────────────────────────────────────
Foundation layer for Arrow’s Impossibility Theorem (UCI version).

* finite agents            (`α`)
* finite alternatives `A`  (with |A| ≥ 3)
* bundled strict orders    (`Preference`)
* profiles & social orders
* lemma `exists_three_distinct` proved without axioms

This file now compiles with **zero holes**.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic   -- for `equivFin`
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

open Classical

universe u

namespace ArrowTypes

/-! ### 1  Parameters -/

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {A : Type u} [Fintype A] [DecidableEq A]



/-! ### 2  Preferences, profiles, social orders -/

/-- An **individual preference**: bundled strict total order on `A`. -/
structure Preference (A : Type u) [DecidableEq A] : Type u where
  rel          : A → A → Prop
  strict_total : IsStrictTotalOrder A rel

instance (A) [DecidableEq A] : CoeFun (Preference A) (fun _ => A → A → Prop) where
  coe p := p.rel

/-- A **profile** assigns each agent their preference. -/
abbrev Profile (α A : Type u) [Fintype α] [DecidableEq α] [DecidableEq A] :=
  α → Preference A

/-- A **social-welfare order** is again a preference on `A`. -/
abbrev SocialWelfare (A : Type u) [DecidableEq A] := Preference A

/-! ### 3  Three distinct alternatives when `|A| ≥ 3` -/

open Finset Fintype

/-- If `|A| ≥ 3`, there exist three pairwise-distinct alternatives. -/
lemma exists_three_distinct (h : (3 : ℕ) ≤ Fintype.card A) :
    ∃ (a b c : A), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  -- `Finset.univ` lists all elements of `A`; shrink it to size 3.
  obtain ⟨s, _sub, hcard⟩ :
      ∃ s : Finset A, s ⊆ (Finset.univ : Finset A) ∧ s.card = 3 :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset A)) (n := 3)
      (by simpa using h)
  -- Decompose the 3-element set into distinct `a b c`.
  rcases Finset.card_eq_three.1 hcard with
    ⟨a, b, c, hab, hac, hbc, _⟩
  exact ⟨a, b, c, hab, hac, hbc⟩

/-! ### 4  A canonical strict total order on any finite type -/


/-- Non-computable equivalence `A ≃ Fin (card A)`. -/
noncomputable def equivFinA : A ≃ Fin (Fintype.card A) :=
  Fintype.equivFin A   -- **no `.symm`**

/-- Canonical strict relation: compare `Fin` indices. -/
noncomputable def canonicalRel (a b : A) : Prop :=
  (equivFinA a).val < (equivFinA b).val

/-- `canonicalRel` is a strict total order (provides `IsStrictTotalOrder`). -/
lemma canonicalRel_strictTotal : IsStrictTotalOrder A canonicalRel := by
  classical
  -- Injectivity of the equivalence, handy for the `=` case.
  have inj : Function.Injective (equivFinA (A := A)) :=
    (equivFinA (A := A)).injective
  -- Build the required record fields explicitly.
  refine
    { trichotomous := ?_,
      irrefl       := ?_,
      trans        := ?_ }
  · -- trichotomy
    intro a b
    dsimp [canonicalRel]
    -- use trichotomy on naturals
    have h := Nat.lt_trichotomy (equivFinA a).val (equivFinA b).val
    cases h with
    | inl hlt      => exact Or.inl hlt
    | inr h' =>
        cases h' with
        | inl heq =>
            -- equal indices ⇒ equal elements by injectivity
            have : a = b := by
              apply inj
              -- Fin equality via value equality
              apply Fin.ext
              simpa using heq
            exact Or.inr (Or.inl this)
        | inr hgt      =>
            exact Or.inr (Or.inr hgt)
  · -- irrefl
    intro a
    dsimp [canonicalRel]
    exact Nat.lt_irrefl _
  · -- trans
    intro a b c hab hbc
    dsimp [canonicalRel] at *
    exact Nat.lt_trans hab hbc

/-- Default preference built from the canonical order. -/
noncomputable def defaultPref : Preference A :=
  ⟨canonicalRel, canonicalRel_strictTotal⟩

/-- Constant profile where **every** voter shares the same preference. -/
@[simp] def constProfile (p : Preference A) : Profile α A := fun _ => p

/-- Every voter has `defaultPref`. Handy lemma. -/
@[simp] lemma const_default_apply (i : α) :
    (constProfile (α:=α) (p:=defaultPref (A:=A)) i) = defaultPref (A:=A) :=
  rfl

end ArrowTypes
