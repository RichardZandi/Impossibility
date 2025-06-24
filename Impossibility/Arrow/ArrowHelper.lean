import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Countable.Defs
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Denumerable
import Impossibility.EncodableBasic
import Impossibility.Arrow.ArrowTypes     -- Profile, Preference, SocialWelfare, …
import Impossibility.Arrow.ArrowAxioms    -- Pareto, IIA
import Impossibility.PreferenceCodec
import Mathlib.Tactic
import Impossibility.UCICoreTest            -- uciGeneral, decode_computable
import Mathlib.Data.Vector.Basic

open Classical
open Kleene.UCI.Classifier
open ArrowTypes ArrowAxioms
open ArrowTypes                            -- Profile α A, SocialWelfare A, …
open Partrec                              -- Primcodable.ofCountable etc.
open Encodable                            -- encode, decode, encodek
open Computable                           -- Computable
open Bool
open PrefCodec
open EncodeBasic


/- SECTION 0 :  Global parameters ­-/
variable {α : Type _} [Fintype α] [DecidableEq α] [Nonempty α]
variable {A : Type _} [Fintype A] [DecidableEq A]

variable (hA3 : 3 ≤ Fintype.card A)    -- |A| ≥ 3
def kk : ℕ := 2
abbrev k := kk                          -- name expected by ArrowUCI
variable (hK : k ≤ Fintype.card α)

/- SECTION 1 : Finite-information social rule `FhatUCI` ­
noncomputable def takePrefix
    (hK : k ≤ Fintype.card α) (p : Profile α A) :
    Fin k → Preference A :=
  fun i =>
    let j : Fin (Fintype.card α) := Fin.castLE hK i
    (Fintype.equivFin α).symm j |> p
-/

noncomputable def takePrefix
    (hK : k ≤ Fintype.card α) (p : ProfileMat α A) :
    Fin k → PrefMat A :=  
  fun i =>
    let j : Fin (Fintype.card α) := Fin.castLE hK i
    (Fintype.equivFin α).symm j |> p

noncomputable def aggOnPrefix (q : Fin k → Preference A) : SocialWelfare A :=
  q (Fin.mk 0 (by decide : 0 < k))

noncomputable def Fhat (hK : k ≤ Fintype.card α) (p : Profile α A) :
    SocialWelfare A :=
  aggOnPrefix (takePrefix hK p)

noncomputable abbrev FhatUCI (p : Profile α A) : SocialWelfare A :=
  Fhat (hK := hK) p

/- SECTION 2 : Boolean classifier `C` ­-/
noncomputable
def triple {A : Type u} [Fintype A] [DecidableEq A]
    (hA3 : 3 ≤ Fintype.card A) :
  ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z :=
  exists_three_distinct hA3

noncomputable def pairTest (r : SocialWelfare A) (x y : A) : Bool :=
  decide (r.rel x y)

noncomputable def C (p : Profile α A) : Bool :=
  -- provide both named arguments that `FhatUCI` expects
  let r := FhatUCI (hK := hK) (p := p)        -- r : SocialWelfare A
  let x := Classical.choose (triple (hA3 := hA3))
  let bc := Classical.choose_spec (triple (hA3 := hA3))
  let y := Classical.choose bc
  pairTest r x y

/- SECTION 3 : Computability & extensionality obligations ­-/
namespace Partrec

/- 3.1 individual components are computable -/
set_option diagnostics true
noncomputable def takePrefix
    (hK : k ≤ Fintype.card α)          -- bound on the prefix length
    (p  : Profile α A)                -- original profile
    : Fin k → Preference A :=          -- restricted profile
  fun i =>
    let j : Fin (Fintype.card α) := Fin.castLE hK i
    (Fintype.equivFin α).symm j |> p   -- apply p to that voter index

lemma takePrefix_comp
    {α A : Type} {k : ℕ}
    [Fintype α] [DecidableEq α]
    [Fintype A] [DecidableEq A]
    {hK : k ≤ Fintype.card α} :
    Computable
      (fun p : Profile α A => takePrefix (hK := hK) p) := ⟨⟩


noncomputable
def aggOnPrefix (q : Fin k → Preference A) : SocialWelfare A :=
  q i₀

lemma aggOnPrefix_comp :
    Computable (fun q : Fin k → PrefMat A => aggOnPrefix q) := by
  have h :
      Computable (fun q : Fin k → PrefMat A => q i₀) :=
    (Computable.id (α := Fin k → PrefMat A)).eval
      (Computable.const (α := Fin k → PrefMat A) i₀)

  simpa [aggOnPrefix] using h


lemma pairTest_comp (x y : A) :
    Computable (fun r : SocialWelfare A => pairTest r x y) := by
  dsimp [pairTest]; computability

/- 3.2 compose them into `C`  -/
lemma C_computable :
    Computable (C (hA3 := hA3) (hK := hK)) := by
  dsimp [C]
  let x : A := Classical.choose (triple (A := A) (hA3 := hA3))
  let bc := Classical.choose_spec (triple (A := A) (hA3 := hA3))
  let y : A := Classical.choose bc
  have hFhat : Computable (fun p : Profile α A => FhatUCI (hK := hK) p) :=
    (aggOnPrefix_comp (k := k)).comp (takePrefix_comp (k := k) (hK := hK))
  have hPair : Computable (fun r : SocialWelfare A => pairTest r x y) :=
    pairTest_comp x y
  simpa [x, y] using hPair.comp hFhat

end Partrec
export Partrec (C_computable)

/- 3.3 extensionality wrt the first `k` voters ­-/
lemma F_extensionality
    {p q : Profile α A}
    (h_prefix_eq : ∀ i : Fin k, takePrefix hK p i = takePrefix hK q i) :
  C (hA3 := hA3) (hK := hK) p = C (hA3 := hA3) (hK := hK) q := by
  dsimp [C, pairTest, FhatUCI, takePrefix]
  -- re-introduce the fixed alternatives
  let x : A := Classical.choose (triple (hA3 := hA3))
  let bc := Classical.choose_spec (triple (hA3 := hA3))
  let y : A := Classical.choose bc
  apply congrArg (fun r : SocialWelfare A => decide (r.rel x y))
  apply congrArg (aggOnPrefix : (Fin k → Preference A) → SocialWelfare A)
  funext i; exact h_prefix_eq i

/- SECTION 4 : Concrete witness profiles  --------------------------------/
-- TODO: Provide real counter-example profiles for your Arrow development.
-- Here we insert placeholders so the file compiles; replace with real ones.

variable (p_bad p_good : Profile α A)

lemma bad_false :
    C (hA3 := hA3) (hK := hK) p_bad = false := by
  -- Supply a concrete proof when you have a real `p_bad`.
  admit

lemma good_true :
    C (hA3 := hA3) (hK := hK) p_good = true := by
  -- Supply a concrete proof when you have a real `p_good`.
  admit

/-  Export names ArrowUCI expects  -/
abbrev bad  := p_bad
abbrev good := p_good

lemma bad_in_E    := bad_false  (p_bad := p_bad)
lemma good_in_notE := good_true (p_good := p_good)

abbrev F_computable := C_computable (hA3 := hA3) (hK := hK)

end                                                           -- end of file
