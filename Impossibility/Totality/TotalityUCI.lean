import Impossibility.UCICoreTest
import Impossibility.Halting.HaltingUCI
import Impossibility.EvolutionInstance
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Bool.Basic
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances
import Kleene2.KleeneFix

open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier
open EvolutionInstance   -- gives us `haltCode`, `divergeCode` if you `open` your other file
open HaltingUCI

namespace TotalityUCI

/--
`decode` on `ℕ` is the identity, hence computable.
We expose it as a lemma because `uciGeneral` needs it.
-/
lemma decode_comp : Computable (fun n : ℕ => (Numbering.decode n : ℕ)) :=
  by
    simpa using (Computable.id)

/-- totally-halting witness  -/
abbrev goodCode : Code := Code.const 1

/-- non-total witness (diverges on input 0)  -/
noncomputable abbrev badCode : Code := divergeCode

/-- bundle any oracle `T` as a classifier – explicit arguments everywhere -/
noncomputable def Φ (T : ℕ → Bool) : Classifiers ℕ := ⟨T⟩

lemma totality_ext
    (T : ℕ → Bool)
    (hT_correct :
      ∀ s : ℕ, T s = true ↔ ∀ n, ((numToCode s).eval n).Dom)
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    T (Numbering.decode (Encodable.encode c₁)) =
    T (Numbering.decode (Encodable.encode c₂)) := by
  simp [Numbering.decode_encode] at *
  have h₁ : T (Encodable.encode c₁) = true ↔ ∀ n, (c₁.eval n).Dom :=
    by
      simpa [numToCode_encode] using
        hT_correct (Encodable.encode c₁)
  have h₂ : T (Encodable.encode c₂) = true ↔ ∀ n, (c₂.eval n).Dom :=
    by
      simpa [numToCode_encode] using
        hT_correct (Encodable.encode c₂)
  have eval_eq : (∀ n, (c₁.eval n).Dom) ↔ ∀ n, (c₂.eval n).Dom := by
    constructor
    · intro h n
      have := congrArg (fun f : ℕ → Part ℕ => f n) hEq
      simpa [this] using h n
    · intro h n
      have := congrArg (fun f : ℕ → Part ℕ => f n) hEq
      simpa [← this] using h n
  by_cases b₁ : T (Encodable.encode c₁) = true
  ·
    have tot₁ : ∀ n, (c₁.eval n).Dom := (h₁).1 b₁
    have tot₂ : ∀ n, (c₂.eval n).Dom := (eval_eq).1 tot₁
    have b₂ : T (Encodable.encode c₂) = true := (h₂).2 tot₂
    simpa [b₁, b₂]
  ·
    have ntot₁ : ¬ ∀ n, (c₁.eval n).Dom := by
      intro tot₁; exact b₁ ((h₁).2 tot₁)
    have ntot₂ : ¬ ∀ n, (c₂.eval n).Dom := by
      intro tot₂; exact ntot₁ ((eval_eq).2 tot₂)
    have b₂ : T (Encodable.encode c₂) = false := by
      by_cases b₂t : T (Encodable.encode c₂) = true
      ·
        have tot₂ : ∀ n, (c₂.eval n).Dom := (h₂).1 b₂t
        exact (ntot₂ tot₂).elim
      ·
        cases h : T (Encodable.encode c₂) <;> simpa [h] using b₂t
    simpa [b₁, b₂]


/-- oracle returns `true` on the always-halting code -/
lemma good_bit
    (T : ℕ → Bool)
    (hT_correct :
      ∀ s : ℕ, T s = true ↔ ∀ n : ℕ, ((numToCode s).eval n).Dom) :
    T (Numbering.decode (Encodable.encode goodCode)) = true := by
  have hTot : ∀ n, (goodCode.eval n).Dom := by
    intro n; simp [goodCode, Code.eval]
  have := (hT_correct (Encodable.encode goodCode)).2
             (by
               simpa [numToCode_encode] using hTot)
  simpa [Numbering.decode_encode] using this

/-- oracle returns `false` on the diverging code -/
lemma bad_bit
    (T : ℕ → Bool)
    (hT_correct :
      ∀ s : ℕ, T s = true ↔ ∀ n, ((numToCode s).eval n).Dom) :
    T (Numbering.decode (Encodable.encode badCode)) = false := by
  -- rewrite the oracle equivalence so the RHS is literally about `badCode`
  have h_equiv :
      T (Encodable.encode badCode) = true ↔
      ∀ n, (badCode.eval n).Dom := by
    simpa [numToCode_encode] using
          hT_correct (Encodable.encode badCode)

  -- `badCode` diverges on input 0 ⇒ it is **not** total
  have not_tot : ¬ (∀ n, (badCode.eval n).Dom) := by
    intro h; exact (divergeCode_diverges 0) (h 0)

  -- therefore the oracle bit cannot be `true`
  have ne_true : T (Encodable.encode badCode) ≠ true := by
    intro htrue
    have tot : ∀ n, (badCode.eval n).Dom := (h_equiv).1 htrue
    exact not_tot tot

  -- only two Bool values left: the bit must be `false`
  cases h : T (Encodable.encode badCode) with
  | true  => exact (ne_true (by simpa using h)).elim
  | false => simpa [Numbering.decode_encode, h]


/-- **main impossibility** – explicit oracle arguments everywhere -/
theorem no_totality_oracle
    (T : ℕ → Bool)
    (hT_comp : Computable T)
    (hT_correct :
      ∀ s : ℕ, T s = true ↔ ∀ n : ℕ, ((numToCode s).eval n).Dom) :
    False :=
  Kleene.UCI.Classifier.uciGeneral (D := ℕ)
    (Φ T)
    hT_comp
    decode_comp
    (totality_ext T hT_correct)
    badCode goodCode
    (bad_bit  T hT_correct)
    (good_bit T hT_correct)

end TotalityUCI
