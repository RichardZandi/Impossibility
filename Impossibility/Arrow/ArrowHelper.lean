/-─────────────────────────────────────────────────────────────────────────
  ArrowHelper.lean  (“production” pseudo-code, fully detailed)
─────────────────────────────────────────────────────────────────────────-/

/- IMPORTS ----------------------------------------------------------------
  Lean’s computability infra, UCI framework, our Arrow types/axioms,
  plus Countable/Encodable for all finite types.
-/
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec        -- Primrec, Partrec, Primcodable, Computable
import Mathlib.Computability.PartrecCode    -- Code
import Impossibility.UCICoreTest            -- uciGeneral, decode_computable
import Impossibility.Arrow.ArrowTypes       -- Profile, Preference, constProfile, …
import Impossibility.Arrow.ArrowAxioms      -- Pareto, IIA
import Mathlib.Data.Countable.Defs          -- Countable for every Fintype
import Mathlib.Logic.Encodable.Basic         -- Encodable
import Mathlib.Data.Fintype.Basic  -- brings in Fintype instances for Pi‐types, so that
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Encodable.Pi




open Classical
open Kleene.UCI.Classifier                 -- Classifiers, uciGeneral
open ArrowTypes                            -- Profile α A, SocialWelfare A, …
open ArrowAxioms                           -- Pareto, IIA

open Partrec                              -- Primcodable.ofCountable etc.
open Encodable                            -- encode, decode, encodek
open Computable                           -- Computable
open Bool


/- SECTION 0 : Global parameters -/
variable {α : Type _} [Fintype α] [DecidableEq α] [Nonempty α]
variable {A : Type _} [Fintype A] [DecidableEq A]

variable (hA3 : 3 ≤ Fintype.card A)  -- |A| ≥ 3
def kk : ℕ := 2
variable (hK : kk ≤ Fintype.card α)

/- SECTION 1 : build the finite‐information rule Fhat -/
noncomputable def takePrefix
  (hK : kk ≤ Fintype.card α)
  (p  : Profile α A) :
  Fin kk → Preference A :=
fun i =>
  let j : Fin (Fintype.card α) := Fin.castLE hK i
  (Fintype.equivFin α).symm j |> p

noncomputable def aggOnPrefix (q : Fin kk → Preference A) : SocialWelfare A :=
  q (Fin.mk 0 (by decide : 0 < kk))

noncomputable def Fhat (hK : kk ≤ Fintype.card α) (p : Profile α A) : SocialWelfare A :=
  aggOnPrefix (takePrefix hK p)

/- SECTION 2 : Turn F̂ into a Bool-classifier C ---------------------------
   We pick three distinct alternatives once and for all, then test
   whether F̂(p) ranks x ≺ y.  That bit is our classifier.
-/
noncomputable
def triple {A : Type u} [Fintype A] [DecidableEq A]
  (hA3 : 3 ≤ Fintype.card A)
  : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z :=
  exists_three_distinct hA3

/-- 2.2  (Optional) a helper to test any pair. -/
noncomputable def pairTest (r : SocialWelfare A) (x y : A) : Bool :=
  decide (r.rel x y)

/-- 2.3  Our Boolean classifier, inlining `triple`. -/
noncomputable def C (p : Profile α A) : Bool :=
  let r := Fhat hK p
  let x := Classical.choose (triple (hA3 := hA3))
  let bc := Classical.choose_spec (triple (hA3 := hA3))
  let y := Classical.choose bc
  pairTest r x y

/- SECTION 3 : Proof‐obligations for `uciGeneral` -------------------------/
namespace Partrec






lemma takePrefix_comp
    (hK : kk ≤ Fintype.card α) :
    Computable (fun p : Profile α A =>
      takePrefix (α := α) (A := A) (hK := hK) p) := by
  dsimp [takePrefix]; computability        -- `computability` tactic suffices

lemma aggOnPrefix_comp :
    Computable (fun q : Fin kk → Preference A =>
      aggOnPrefix (A := A) (kk := kk) q) := by
  dsimp [aggOnPrefix]; computability

lemma pairTest_comp (x y : A) :
    Computable (fun r : SocialWelfare A => pairTest r x y) := by
  dsimp [pairTest]; computability






/-- `pairTest` is computable once the two alternatives are fixed. -/
lemma pairTest_comp (x y : A) :
    Computable (fun r : SocialWelfare A => pairTest r x y) := by
  dsimp [pairTest]
  -- `r.rel x y` is a Boolean (by `decide`), so projections are computable
  exact
    (Computable.const x).choose -- the two `Computable.const`’s give Lean all it needs

-- 3) Finally, compose them (decode ↦ takePrefix ↦ aggOnPrefix ↦ pairTest)
lemma C_computable :
    Computable (C (hA3 := hA3) (hK := hK)) := by
  -- Unfold the definition once so that the constants `x` and `y` are visible.
  dsimp [C]

  -- ------------------------------------------------------------------
  -- Step 0: name the two fixed alternatives *once and for all*.
  -- ------------------------------------------------------------------
  let x : A := Classical.choose  (triple (A := A) (hA3 := hA3))
  let bc := Classical.choose_spec (triple (A := A) (hA3 := hA3))
  let y : A := Classical.choose bc

  -- ------------------------------------------------------------------
  -- Step 1: `Fhat` itself is computable – compose the two earlier lemmas
  -- ------------------------------------------------------------------
  have hFhat : Computable (fun p : Profile α A => Fhat (hK := hK) p) :=
    (aggOnPrefix_comp (kk := kk)).comp (takePrefix_comp (kk := kk) (hK := hK))

  -- ------------------------------------------------------------------
  -- Step 2: comparing the two *fixed* alternatives is computable
  -- ------------------------------------------------------------------
  have hPair : Computable (fun r : SocialWelfare A => pairTest r x y) :=
    pairTest_comp x y

  -- ------------------------------------------------------------------
  -- Step 3: put the two pieces together
  -- ------------------------------------------------------------------
  simpa [x, y] using hPair.comp hFhat



/- ②  DECODER computability  ------------------------------------------------
   This is already provided by UCICore:
     `decode_computable : Computable (λ n => decode n : Profile α A)`
-/
-- #check decode_computable : Computable (λ n => decode n : Profile α A)

/- ③  EXTENSIONALITY w.r.t. prefix-agreement  ----------------------------
   If two profiles p, q agree on the first kk voters, then `takePrefix hK p = takePrefix hK q`,
   so `Fhat p = Fhat q` and hence `C p = C q`.
-/
lemma C_extensionality
  {p q : Profile α A}
  (h_prefix_eq : ∀ i : Fin kk,
     takePrefix hK p i = takePrefix hK q i)
  : C (hA3 := hA3) (hK := hK) p = C (hA3 := hA3) (hK := hK) q := by
  dsimp [C, pairTest, Fhat, takePrefix]
  apply congrArg (fun r : SocialWelfare A => decide (r.rel x y))
  apply congrArg (aggOnPrefix : (Fin kk → Preference A) → SocialWelfare A)
  funext i
  exact h_prefix_eq i


lemma bad_false : C (hA3 := hA3) (hK := hK) p_bad = true := by
  -- Unfold C down to `decide ((prefXY x y _).rel x y)`
  dsimp [C, pairTest, Fhat, p_bad, takePrefix, aggOnPrefix]
  -- prefXY_rel: (prefXY x y _).rel x y = true
  -- decide_eq_true: decide true = true
  simp [prefXY_rel, decide_eq_true]


lemma good_true : C (hA3 := hA3) (hK := hK) p_good = true := by
  dsimp [C, pairTest, Fhat, p_good, takePrefix, aggOnPrefix]
  let x'  := Classical.choose (triple (hA3 := hA3))
  let bc' := Classical.choose_spec (triple (hA3 := hA3))
  let y'  := Classical.choose bc'
  -- Now unanimous y'≺x' by Pareto
  have hyx : (Fhat hK p_good).rel y' x' :=
    (inferInstance : Pareto (Fhat hK)).pareto p_good y' x' fun _ => rfl
  simp [hyx, decide_eq_false]
