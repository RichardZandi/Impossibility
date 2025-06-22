/-
Impossibility/Arrow/ArrowProof.lean
────────────────────────────────────
Arrow’s theorem skeleton.

* DecisivePair / Dxy definitions
* Lemma `nonempty_decisive`    (→ will prove next)
* Theorem `arrow_dictator`     (final goal — still `admit`)

Everything compiles; we’ll replace the two placeholders (`sorry`, `admit`)
incrementally.
-/
import Impossibility.Arrow.ArrowTypes
import Impossibility.Arrow.ArrowAxioms
import Mathlib.Data.List.Basic

open Classical ArrowTypes

universe u

variable {α A : Type u}
variable [Fintype α] [DecidableEq α] [Nonempty α]
variable [Fintype A] [DecidableEq A]

/-- Swap the arguments of a relation. -/
private def flipRel (r : A → A → Prop) : A → A → Prop :=
  fun a b => r b a

/-- If `r` is a strict-total order, then the relation with its arguments
    swapped is also strict-total. -/
private lemma flipRel_strictTotal
    {r : A → A → Prop} (h : IsStrictTotalOrder A r) :
    IsStrictTotalOrder A (flipRel r) := by
  classical
  refine
    { trichotomous := ?_,
      irrefl       := ?_,
      trans        := ?_ }
  · -- trichotomy
    intro a b
    -- original trichotomy on `r`
    have hTri := h.trichotomous a b
    -- rearrange the disjunctions to fit the flipped relation
    cases hTri with
    | inl rab =>               -- `r a b`
        exact Or.inr (Or.inr rab)   -- becomes third case
    | inr h' =>
        cases h' with
        | inl hEq =>            -- `a = b`
            exact Or.inr (Or.inl hEq)   -- middle case
        | inr rba =>            -- `r b a`
            exact Or.inl rba            -- first case
  · -- irrefl
    intro a
    dsimp [flipRel]
    exact h.irrefl a
  · -- trans
    intro a b c hab hbc
    dsimp [flipRel] at *
    -- want `r c a`; we have `r b a` and `r c b`
    exact h.trans _ _ _ hbc hab

noncomputable def prefXY (x y : A) : Preference A := by
  classical
  -- If canonical order already has x≺y, keep it; otherwise flip it.
  by_cases h : canonicalRel x y
  · exact defaultPref
  · exact
      ⟨flipRel canonicalRel,
       flipRel_strictTotal canonicalRel_strictTotal⟩

/-- Key fact: **when `x ≠ y`**, `prefXY x y` ranks `x ≺ y`. -/
lemma prefXY_rel {x y : A} (hxy : x ≠ y) :
    (prefXY x y).rel x y := by
  classical
  by_cases h : canonicalRel x y
  · -- canonical order already ranks x ≺ y, and `prefXY` kept it
    simpa [prefXY, h, defaultPref] using h
  · -- we flipped the order, so need `canonicalRel y x`
    have tri := (canonicalRel_strictTotal).trichotomous x y
    -- trichotomy plus `¬ canonicalRel x y` and `x ≠ y`
    -- yields `canonicalRel y x`
    have hyx : canonicalRel y x := by
      cases tri with
      | inl hlt       => exact (h hlt).elim
      | inr h' =>
          cases h' with
          | inl hEq     => exact (hxy hEq).elim
          | inr hgt     => exact hgt
    -- flipped relation: flipRel canonicalRel x y ≡ canonicalRel y x
    simpa [prefXY, h, flipRel] using hyx

/-- `DecisivePair F i x y` means:
    whenever voter `i` strictly prefers `x ≺ y` in a profile `p`,
    the social ranking produced by `F` also satisfies `x ≺ y`. -/
def DecisivePair
    (F : Profile α A → SocialWelfare A) (i : α) (x y : A) : Prop :=
  ∀ p, (p i).rel x y → (F p).rel x y

/-- `Dxy F x y` is the set of agents decisive for the ordered pair `(x,y)`. -/
def Dxy
    (F : Profile α A → SocialWelfare A) (x y : A) : Set α :=
  { i | DecisivePair F i x y }

/-! ### 2  First lemma (to be proved next) -/

/- After every voter has been switched from `q` to `p`,
    the profile `switch enum.length` coincides with `p`. -/


-- variable {α A : Type} [Fintype α] [DecidableEq α]
variable {α A : Type} [Fintype α] [DecidableEq α]
variable (p q : Profile α A)
variable (F : Profile α A → SocialWelfare A)
variable (x y : A) (p q : Profile α A)
noncomputable def enum : List α :=  (Finset.univ : Finset α).toList
noncomputable def switch
    (p q : Profile α A) (k : ℕ) : Profile α A :=
  fun i => if h : ((i : α) ∈ enum.take k) then p i else q i
def enumLength : Nat := Finset.card (Finset.univ : Finset α)
/-- `enum.length` equals `enumLength` (cardinality of the finset). -/
lemma length_enum : (enum : List α).length = enumLength (α := α) := by
  dsimp [enumLength, enum]
  simp  -- `card_toList`


lemma switch_eq_end : switch p q (enumLength (α := α)) = p := by
  funext i
  have hmem : (i : α) ∈ enum.take (enumLength (α := α)) := by
    have : (i : α) ∈ enum := by
      have : (i : α) ∈ (Finset.univ : Finset α) := by simp
      simpa [enum, Finset.mem_toList] using this
    rwa [← length_enum, List.take_length]
  simp [switch, hmem]

/-
lemma nonempty_decisive
    {F : Profile α A → SocialWelfare A}
    (hPareto : Pareto F) (hIIA : IIA F)
    (x y : A) :
    (Dxy F x y).Nonempty := by
  classical
  /- Handle the degenerate case x = y first. -/
  by_cases hxy_eq : x = y
  · subst hxy_eq
    -- Any agent works, because `rel x x` is impossible.
    let i0 : α := Classical.arbitrary α
    have dec : DecisivePair F i0 x x := by
      intro p hpxx
      -- `rel` is irreflexive, derive contradiction.
      have : False := (p i0).strict_total.irrefl _ hpxx
      exact this.elim
    exact ⟨i0, dec⟩
  ·
    -- Distinct pair: x ≠ y
    have hxy : x ≠ y := hxy_eq
    -- unanimous profile with prefXY ⇒ society ranks x≺y
    let p : Profile α A := constProfile (α := α) (prefXY x y)
    have hp : (F p).rel x y := by
      apply hPareto p x y
      intro _; simpa [p, prefXY_rel hxy] using prefXY_rel hxy
    -- unanimous flipped profile ⇒ society ranks y≺x
    let q : Profile α A :=
      constProfile (α := α)
        ⟨flipRel (prefXY x y).rel,
         flipRel_strictTotal (prefXY x y).strict_total⟩
    have hq : (F q).rel y x := by
      apply hPareto q y x
      intro _; simp [q, flipRel, prefXY_rel hxy]
    -- Apply finite flip-index helper to get a decisive voter
    rcases exists_flip_index hIIA x y p q hp hq with ⟨i, hi⟩
    exact ⟨i, hi⟩
  -/
