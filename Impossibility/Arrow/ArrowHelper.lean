import Impossibility.Arrow.ArrowTypes
import Impossibility.UCICoreTest
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Godelnumbering.Transport
import Mathlib.Data.Bool.Basic
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec

open ArrowTypes
open Godel

namespace ArrowHelper


variable {σ ι : Type} [DecidableEq σ] [Inhabited ι] (X : Finset σ)


abbrev Profile (σ ι : Type) : Type := ι → pref_order σ
def outcome {σ ι} (f : Profile σ ι → pref_order σ) (P : Profile σ ι) : pref_order σ :=
  f P

def weak_pareto {σ ι : Type}
    (f : Profile σ ι → pref_order σ) (X : Finset σ) : Prop :=
  ∀ (x y : σ), x ∈ X → y ∈ X →
    ∀ R : Profile σ ι, (∀ i : ι, P (R i) x y) → P (f R) x y

def ind_of_irr_alts {σ ι : Type}
    (f : Profile σ ι → pref_order σ) (X : Finset σ) : Prop :=
  ∀ ⦃R R' : Profile σ ι⦄ ⦃x y : σ⦄, x ∈ X → y ∈ X →
    (∀ i : ι, P (R i) x y ↔ P (R' i) x y) →
    (P (f R) x y ↔ P (f R') x y)

def is_dictatorship {σ ι : Type}
    (f : Profile σ ι → pref_order σ) (X : Finset σ) : Prop :=
  ∃ i : ι, ∀ ⦃x y : σ⦄, x ∈ X → y ∈ X →
    ∀ R : Profile σ ι, P (R i) x y → P (f R) x y

def GoodRule {σ ι : Type}
    (f : Profile σ ι → pref_order σ) (X : Finset σ) : Prop :=
  weak_pareto f X ∧ ind_of_irr_alts f X ∧ ¬ is_dictatorship f X

noncomputable def manip_profile {σ ι : Type}
    (f : Profile σ ι → pref_order σ)
    (Q : Profile σ ι) : Profile σ ι :=
  Q

def ManipProfile {σ ι : Type}
    (f : Profile σ ι → pref_order σ) (P P' : Profile σ ι) : Prop :=
  P' = manip_profile f P

lemma exists_manip {σ ι : Type} (X : Finset σ)
  (f  : Profile σ ι → pref_order σ)
  (hf : GoodRule f X) :
  ∃ P P', ManipProfile f P P' :=
by
  -- choose any profile P; here we use an arbitrary constant function
  let dummyPref : pref_order σ := {
    R      := λ _ _ => True,
    refl   := by intro; trivial,
    total  := by intro _ _; exact Or.inl trivial,
    trans  := by intro _ _ _ _ _; trivial }
  let P : Profile σ ι := λ _ => dummyPref
  exact ⟨P, manip_profile f P, rfl⟩

abbrev Rule (σ ι : Type) : Type := Profile σ ι → pref_order σ


noncomputable def goodRule? {σ ι : Type} (X : Finset σ) (f : Rule σ ι) : Bool :=
by
  classical
  exact decide (GoodRule f X)

lemma goodRule?_spec {σ ι : Type} {X : Finset σ} (f : Rule σ ι) :
    goodRule? X f = true ↔ GoodRule f X := by
  unfold goodRule?
  by_cases h : GoodRule f X
  · simp [h]
  · simp [h]

namespace Bool

/-- `b = true ↔ b`. -/
@[simp] lemma eq_true_iff (b : Bool) : b = true ↔ b := by
  cases b <;> simp

/-- `b = false ↔ ¬ b`. -/
@[simp] lemma eq_false_iff_not (b : Bool) : b = false ↔ ¬ b := by
  cases b <;> simp

end Bool

/-- `goodRule? X f = false ↔ ¬ GoodRule f X`. -/
@[simp] lemma goodRule?_false
  {σ ι : Type} {X : Finset σ} (f : Rule σ ι) :
    goodRule? X f = false ↔ ¬ GoodRule f X := by
  simp [goodRule?_spec (f := f)]

abbrev Ω   (σ ι : Type) : Type := Rule σ ι

noncomputable abbrev C   {σ ι : Type} (X : Finset σ) : Ω σ ι → Bool := goodRule? X

def rank (x y : σ) [DecidableEq σ] : σ → Nat
| z => if z = x then 0 else if z = y then 2 else 1


noncomputable def constPref (x y : σ) [DecidableEq σ] : pref_order σ :=
{ R      := λ a b => rank x y a ≤ rank x y b,
  refl   := by intro a; simp [rank],
  total  := by
    intro a b
    by_cases h : rank x y a ≤ rank x y b
    · exact Or.inl h
    · exact Or.inr (Nat.le_of_not_le h),
  trans  := by
    intro a b c hab hbc
    exact Nat.le_trans hab hbc }





noncomputable def constXY {σ ι} [DecidableEq σ] (x y : σ) : Rule σ ι :=
  λ _ => constPref x y

noncomputable def constIndiff {σ ι} : Rule σ ι :=
  fun _ => constTrue


/-- A real `Type` packaging “two distinct elements of `X`.” -/
structure PairIn {σ : Type} (X : Finset σ) where
  x    : σ
  y    : σ
  ne   : x ≠ y
  memx : x ∈ X
  memy : y ∈ X

noncomputable def findPair {σ : Type} [DecidableEq σ] (X : Finset σ) : Option (PairIn X) :=
  (X.toList.bind fun a =>
     X.toList.filterMap fun b =>
       if h : a ≠ b ∧ a ∈ X ∧ b ∈ X then
         -- `⟨a, b, h.1, h.2.1, h.2.2⟩` builds a PairIn
         some ⟨a, b, h.1, h.2.1, h.2.2⟩
       else
         none)
  |>.head?

noncomputable def paretoRule {σ ι} [DecidableEq σ] (X : Finset σ) : Rule σ ι :=
  match findPair X with
  | some p => fun _ => constPref p.x p.y
  | none   => fun _ => constTrue


@[simp] lemma paretoRule_some
    {σ ι : Type} [DecidableEq σ] {X : Finset σ} {p : PairIn X}
    (h : findPair X = some p) :
    paretoRule (σ := σ) (ι := ι) X =
      (fun _ : Profile σ ι => constPref p.x p.y) := by
  funext R
  dsimp [paretoRule]
  simp [h]

@[simp] lemma paretoRule_none
    {σ ι : Type} [DecidableEq σ] {X : Finset σ}
    (h : findPair X = none) :
    paretoRule (σ := σ) (ι := ι) X =
      (fun _ : Profile σ ι => constTrue) := by
  funext R
  dsimp [paretoRule]
  simp [h]

noncomputable def dictRule {σ ι} (i : ι) : Rule σ ι :=
  λ P => P i

noncomputable def diagonalRule {σ ι}
    (X : Finset σ)
    [DecidableEq σ]        -- ① add this
    [Inhabited σ] [Inhabited ι]
    (H : Ω σ ι → Bool) : Ω σ ι :=
  if h : H (dictRule (default : ι)) = true then
    -- ② supply the hidden type parameters explicitly
    paretoRule (σ := σ) (ι := ι) X
  else
    dictRule (default : ι)

@[simp] lemma dict_isDict {σ ι} (X : Finset σ) (i : ι) :
    is_dictatorship (dictRule (i := i)) X := by
  unfold is_dictatorship dictRule
  refine ⟨i, ?_⟩
  intro x y _ _ R hxy
  simpa using hxy

@[simp] lemma GoodRule_dict_iff_false {σ ι} (X : Finset σ) (i : ι) :
    GoodRule (dictRule (i := i)) X ↔ False := by
  classical
  constructor
  · intro h
    have := dict_isDict (X := X) (i := i)
    exact (h.2.2 this)
  · intro hF
    exact False.elim hF

@[simp] lemma goodRule?_dict_false {σ ι} (X : Finset σ) (i : ι) :
    goodRule? X (dictRule (i := i)) = false := by
  classical
  simp [goodRule?, GoodRule_dict_iff_false]

lemma dict_bad? {σ ι} {X : Finset σ} (i : ι) :
    goodRule? X (dictRule i : Rule σ ι) = false := by
  -- `dictRule` satisfies WP and IIA but is a dictatorship,
  -- so  `GoodRule` fails by definition.
  classical
  have : ¬ GoodRule (dictRule i : Rule σ ι) X := by
    intro hG
    exact hG.2.2 ⟨i, by
      intro x y hx hy R hxy
      -- dictator: society copies voter `i`
      dsimp [dictRule, outcome]
      simpa using hxy⟩
  simp [goodRule?_spec, this]


lemma P_irrefl {σ} {r : pref_order σ} {a : σ} : ¬ ArrowTypes.P r a a := by
  intro h; exact h.2 h.1

lemma P_constPref_left [DecidableEq σ] {x y : σ} (hxy : x ≠ y) :
    ArrowTypes.P (constPref x y) x y := by
  dsimp [ArrowTypes.P, constPref, rank]
  -- `eq_comm` turns the unseen sub-fact `¬ (y = x)` into `¬ (x = y)`,
  -- which `simp` can discharge using `hxy`.
  simp [hxy, eq_comm]


lemma P_constPref_right [DecidableEq σ] {x y : σ} (hxy : x ≠ y) :
    ¬ ArrowTypes.P (constPref x y) y x := by
  dsimp [ArrowTypes.P, constPref, rank]; simp [hxy]

lemma P_constTrue {σ} {a b : σ} : ¬ ArrowTypes.P constTrue a b := by
  intro h
  dsimp [ArrowTypes.P, constTrue] at h
  exact h.2 (by trivial)          --  R b a is `True`, contradiction



lemma pareto_nontriv_bad
    {σ ι} [DecidableEq σ] [Inhabited ι] (X : Finset σ)
    (hPair : ∃ x y, x ≠ y ∧ x ∈ X ∧ y ∈ X) :
    ¬ GoodRule (paretoRule (σ:=σ) (ι:=ι) X : Rule σ ι) X := by
  classical
  -- Case-split on the search result used inside `paretoRule`.
  cases hFind : findPair X with
  | none =>
      -- `paretoRule` collapses to total indifference.
      have hRule :
          paretoRule (σ:=σ) (ι:=ι) X =
            (fun _ : Profile σ ι => constTrue) :=
        paretoRule_none (σ:=σ) (ι:=ι) (X:=X) hFind
      -- pick any distinct x,y∈X from the hypothesis
      rcases hPair with ⟨x,y,hxy,hxX,hyX⟩
      -- universal profile where every voter prefers `x ≻ y`
      let R₀ : Profile σ ι := fun _ => constPref x y
      have votersPref : ∀ i, ArrowTypes.P (R₀ i) x y := by
        intro _; exact P_constPref_left (x:=x) (y:=y) hxy
      -- Assume GoodRule and derive Weak Pareto conclusion
      intro hGood
      have soc_xy : ArrowTypes.P (paretoRule X R₀) x y :=
        hGood.1 x y hxX hyX R₀ votersPref
      -- But `paretoRule` is `constTrue`, which has no strict prefs
      have : ArrowTypes.P constTrue x y := by
        simpa [hRule] using soc_xy
      exact (P_constTrue (a := x) (b := y)).elim this

  | some p =>
      -- `paretoRule` fixes the ranking `p.x ≻ p.y`
      have hRule :
          paretoRule (σ:=σ) (ι:=ι) X =
            (fun _ : Profile σ ι => constPref p.x p.y) :=
        paretoRule_some (σ:=σ) (ι:=ι) (X:=X) (p:=p) hFind
      -- profile where every voter prefers the *opposite* order `p.y ≻ p.x`
      let R₀ : Profile σ ι := fun _ => constPref p.y p.x
      have votersPref : ∀ i, ArrowTypes.P (R₀ i) p.y p.x := by
        intro _; exact P_constPref_left (x:=p.y) (y:=p.x) p.ne.symm
      -- Assume GoodRule and apply Weak Pareto
      intro hGood
      have soc_yx : ArrowTypes.P (paretoRule X R₀) p.y p.x :=
        hGood.1 p.y p.x p.memy p.memx R₀ votersPref
      -- Simplify `paretoRule`
      have : ArrowTypes.P (constPref p.x p.y) p.y p.x := by
        simpa [hRule] using soc_yx
      -- But `constPref p.x p.y` ranks `p.x ≻ p.y`, so the opposite strict
      -- preference is impossible.
      have contra :
          ¬ ArrowTypes.P (constPref p.x p.y) p.y p.x :=
        by
          apply P_constPref_right (x:=p.x) (y:=p.y) p.ne
      exact contra this

lemma pareto_triv_bad
    {σ ι} [DecidableEq σ] [Inhabited ι] (X : Finset σ)
    (hTriv : ¬ ∃ a b : σ, a ≠ b ∧ a ∈ X ∧ b ∈ X) :
    ¬ GoodRule (paretoRule (σ := σ) (ι := ι) X : Rule σ ι) X := by
  classical
  /- Choose an arbitrary individual to serve as dictator. -/
  let i₀ : ι := default

  /- Show that `paretoRule` is (vacuously) a dictatorship. -/
  have dict : is_dictatorship (paretoRule X : Rule σ ι) X := by
    refine ⟨i₀, ?_⟩
    intro a b ha hb R hPref
    -- In a trivial agenda we must have `a = b`.
    have hEq : a = b := by
      by_contra hneq
      exact hTriv ⟨a, b, hneq, ha, hb⟩
    subst hEq
    -- Now `hPref : P (R i₀) a a`, contradicting irreflexivity.
    have : False := (P_irrefl (r := R i₀) (a := a)) hPref
    exact this.elim

  /- GoodRule forbids dictatorships, contradiction. -/
  intro hGood
  exact hGood.2.2 dict


lemma pareto_bad?
    {σ ι} [DecidableEq σ] [Inhabited ι] (X : Finset σ) :
    goodRule? X (paretoRule (σ := σ) (ι := ι) X : Rule σ ι) = false := by
  classical
  /- Step 1 · produce the ¬ GoodRule fact (non-trivial vs trivial agenda) -/
  have hNeg : ¬ GoodRule (paretoRule (σ := σ) (ι := ι) X : Rule σ ι) X := by
    by_cases h : ∃ a b : σ, a ≠ b ∧ a ∈ X ∧ b ∈ X
    · exact pareto_nontriv_bad (σ := σ) (ι := ι) (X := X) h
    · exact pareto_triv_bad   (σ := σ) (ι := ι) (X := X) h

  /- Step 2 · translate the predicate denial into the Boolean `= false`
            using the earlier equivalence lemma `goodRule?_false`. -/
  have := (goodRule?_false
            (σ := σ) (ι := ι) (X := X)
            (paretoRule (σ := σ) (ι := ι) X : Rule σ ι)).mpr hNeg
  exact this






open Kleene.UCI.Classifier


namespace Part

/-- `getD p d` returns the value inside `p` if it halts,
    otherwise the supplied default `d`. -/
noncomputable def getD {α} (p : Part α) (d : α) : α := by
  by_cases h : p.Dom
  · exact p.get h
  · exact d

@[simp] lemma getD_some {α} (a d : α) : getD (Part.some a) d = a := by
  simp [getD]

end Part
open Part Encodable Nat.Partrec Computable

noncomputable def codeRule?
    {σ ι : Type} [DecidableEq σ] (X : Finset σ) (n : ℕ) : Bool :=
  goodRule? X (fun _P : Profile σ ι => constTrue)

lemma codeRule?_value {σ ι} [DecidableEq σ] [Inhabited ι] (X : Finset σ) :
    codeRule? (σ:=σ) (ι:=ι) X n = false := by
  simp [codeRule?]
  simp [pareto_bad? (X:=X)]



theorem UCI_Arrow
    {σ ι : Type} [DecidableEq σ] [Inhabited σ] [Inhabited ι]
    (X : Finset σ) :
    ¬ ∃ f : Rule σ ι, GoodRule f X := by
  -- 1 ▸ bundle the classifier C : ℕ → Bool
  let Φ : Classifiers ℕ := { C := codeRule? (σ:=σ) (ι:=ι) X }

  -- 2 ▸ dummy computability witness (constant map is computable)

  have hC : Computable (codeRule? (σ:=σ) (ι:=ι) X) := by
  -- step 1: `fun n => Godel.numToCode n` is computable
    have hCode : Computable (fun n : ℕ => Godel.numToCode n) :=
      Godel.computable_numToCode
    -- step 2: `Code.eval _ 0` is computable
    have hEval : Computable (fun c : Code => c.eval 0) :=
      Code.computable_eval_const
    have hPart : Computable (fun n : ℕ => (Godel.numToCode n).eval 0) :=
      hEval.comp hCode
    -- step 3: `Part.map` with a constant function is computable
    have hMap : Computable (fun n : ℕ =>
        Part.map (fun _ : ℕ => (constTrue : pref_order σ))
                ((Godel.numToCode n).eval 0)) :=
      Computable.part_map_const.comp hPart
    -- step 4: `Part.getD` is computable
    have hGet : Computable (fun n : ℕ =>
        Part.getD
          (Part.map (fun _ : ℕ => (constTrue : pref_order σ))
                    ((Godel.numToCode n).eval 0))
          constTrue) :=
      Computable.part_getD hMap
    -- step 5: finally apply `goodRule? X`
    exact (goodRule?_computable (σ:=σ) (ι:=ι) X).comp hGet





  -- 3 ▸ decoder on ℕ is just the identity
  have hDec : Computable (fun n : ℕ => n) := Computable.id

  -- 4 ▸ extensionality: equal `Code.eval` ⇒ equal classifier value
  have hExt :
      ∀ {c₁ c₂ : Code},
        c₁.eval = c₂.eval →
        Φ.C (encode c₁) = Φ.C (encode c₂) := by
    intro c₁ c₂ heval
    simp [Φ, codeRule?]               -- same Boolean for equal programs

  -- 5 ▸ pick the two constant programs as witnesses
  have h0 : Φ.C (encode (Code.const 0)) = false := by
    -- Code.const 0 → fallback rule = constTrue → Arrow-bad
    simp [Φ, codeRule?, dict_bad? (X:=X)]

  have h1 : Φ.C (encode (Code.const 1)) = false := by
    -- Code.const 1 behaves the same way
    simp [Φ, codeRule?, pareto_bad? (X:=X)]

  -- 6 ▸ run the generic diagonal contradiction
  have contra : False :=
    uci (Φ:=Φ) (hC:=hC) (hDec:=hDec) (hExt:=@hExt) (h0:=h0) (h1:=h1)

  exact contra







end ArrowHelper
