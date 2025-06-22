import Impossibility.EvolutionInstance
import Kleene.UCI.Classifier
import Godelnumbering.Transport
import Mathlib.Data.Bool.Basic      -- `decide`

open EvolutionInstance Kleene.UCI.Classifier
open Godel FirstOrder Language

/-! ## 1.  Arithmetic language and an **axiomatic** provability oracle -/

abbrev L := arithLang
abbrev Sentence := Sentence L

/-- Syntactic provability (left abstract). -/
constant Provable : Sentence → Prop

/-- `⊤` is provable. -/
axiom Provable_true : Provable (⊤ : Sentence)

/-- `⊥` is **not** provable (consistency). -/
axiom Provable_not_false : ¬ Provable (⊥ : Sentence)

/-- Classical decidability of provability (for `decide`). -/
axiom Provable_decidable (φ : Sentence) : Decidable (Provable φ)
instance : DecidablePred Provable := Provable_decidable

/-! ## 2.  Classifier Φ via the total evaluator `evalTotal 0` -/

noncomputable def U := evalTotal 0           -- total, extensional

/-- Ask whether the sentence produced by program `idx` on input `0`
    is provable. -/
noncomputable def provableOut? (idx : ℕ) : Bool :=
  let n := U idx 0
  decide (Provable (decodeSentence (L:=L) n))

/-! ## 3.  UCI ingredients ------------------------------------------------- -/

/-- **False premise:** the classifier is (total) computable.
    (UCI will refute this.) -/
axiom provableOut?_computable : Computable provableOut?

/-- Extensionality inherited from `[ExtensionalF (E 0)]`. -/
lemma provableOut?_ext {c₁ c₂ : Code}
    (h : c₁.eval = c₂.eval) :
    provableOut? (encode c₁) = provableOut? (encode c₂) := by
  -- `evalTotal` respects `eval`-equality via the bundled instance
  have hU : U (encode c₁) 0 = U (encode c₂) 0 := by
    have := (inferInstance : ExtensionalF (E 0))
    simpa [U, encode] using this.ext _ _ h 0
  simpa [provableOut?, hU]

/-  Witness codes required by UCI  -/

/-- *Bad* code: always outputs the Gödel number of `⊥`. -/
abbrev badCode : Code := Code.const (encodeSentence (⊥ : Sentence))

/-- *Good* code: always outputs the Gödel number of `⊤`. -/
abbrev goodCode : Code := Code.const (encodeSentence (⊤ : Sentence))

/-- Classifier value on the *bad* code is `false`. -/
lemma pred_bad : provableOut? (encode badCode) = false := by
  have : Decidable (Provable (⊥ : Sentence)) := Provable_decidable _
  have h : Provable (⊥ : Sentence) = False := by
    apply propext
    exact ⟨Provable_not_false, by intro contra; exact False.elim (Provable_not_false contra)⟩
  simp [provableOut?, badCode, Provable_not_false, h]

/-- Classifier value on the *good* code is `true`. -/
lemma pred_good : provableOut? (encode goodCode) = true := by
  have : Provable (⊤ : Sentence) := Provable_true
  simp [provableOut?, goodCode, this]

/-! ## 4.  Gödel contradiction via UCI ------------------------------------ -/

theorem godel_impossibility : False :=
  uciGeneral
    (Φ     := ⟨provableOut?⟩)
    (hC    := provableOut?_computable)             -- assumption to refute
    (hDec  := decodeSentence_computable (L:=L))    -- from Transport.lean
    (hExt  := provableOut?_ext)
    badCode goodCode
    pred_bad pred_good
