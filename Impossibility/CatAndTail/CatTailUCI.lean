import Mathlib.Computability.Primrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Bool.Basic
import Godelnumbering.Godel
import Godelnumbering.Instances
import Impossibility.Evolution
import Impossibility.CatAndTail.CatTailWitness           -- uses `E.reacts`
import UCI.UCICore

open Classical Evolution Nat.Partrec Code
open Kleene.UCI.Classifier
open Godel

set_option autoImplicit false

namespace CatTailUCI

/-- `good? E s` is `true` exactly when the system `E`, started from the
    numeric state `s`, maps the input `0` to the value `1`. -/
@[inline] def good? (E : Evolution) : ℕ → Bool :=
  fun s => (E.F s 0) == 1

abbrev UClassifier := Kleene.UCI.Classifier.Classifiers
@[inline] def mkClassifier (E : Evolution) : UClassifier ℕ := ⟨good? E⟩

/-! ### 1  Computability of `good?` (needs `[ComputableF E]`) -/
lemma good?_computable (E : Evolution) [ComputableF E] :
    Computable (good? E) := by
  -- `s ↦ E.F s 0`
  have hF   : Computable (fun p : ℕ × ℕ => E.F p.1 p.2) :=
    (ComputableF.comp : _)
  have hF0  : Computable (fun s : ℕ => E.F s 0) :=
    hF.comp (Computable.pair Computable.id (Computable.const 0))
  -- `x ↦ x == 1`
  have hEq1 : Primrec (fun x : ℕ => x == 1) := by
    have hBeq : Primrec (fun p : ℕ × ℕ => p.fst == p.snd) :=
      Primrec₂.comp Primrec.beq Primrec.fst Primrec.snd
    have hPair : Primrec (fun x : ℕ => (x, (1 : ℕ))) :=
      Primrec.pair Primrec.id (Primrec.const 1)
    simpa using hBeq.comp hPair
  exact (hEq1.to_comp).comp hF0

/-! ### 2  Extensionality (needs `[ExtensionalF E]`) -/
lemma good?_ext (E : Evolution) [ExtensionalF E] :
    ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
      good? E (Numbering.decode (Encodable.encode c₁)) =
      good? E (Numbering.decode (Encodable.encode c₂)) := by
  intro c₁ c₂ hEq
  -- extensionality of F, specialised at input 0
  have hF0 := (ExtensionalF.ext (E := E) hEq) 0
  simp [good?, hF0]

/-! ### 3  Classifier values on the two constant codes -/
lemma good?_code0 (E : Evolution) :
    good? E (Numbering.decode (Encodable.encode (Code.const 0))) = false := by
  have hEval : (Code.const 0).eval 0 = pure 0 := by simp
  have hF    : E.F (Encodable.encode (Code.const 0)) 0 = 0 :=
    E.reacts hEval
  simp [good?, hF]

lemma good?_code1 (E : Evolution) :
    good? E (Numbering.decode (Encodable.encode (Code.const 1))) = true := by
  have hEval : (Code.const 1).eval 0 = pure 1 := by simp
  have hF    : E.F (Encodable.encode (Code.const 1)) 0 = 1 :=
    E.reacts hEval
  simp [good?, hF]

/-! ### 4  Cat-and-Tail impossibility (requires both evidences) -/
@[simp] theorem cat_and_tail
    (E : Evolution) [ComputableF E] [ExtensionalF E] :
    ¬ ∃ π : Evolution.Predictor E.F, True := by
  intro _hπ
  let Φ := mkClassifier E
  have hC      := good?_computable E
  have hDecode : Computable (fun n : ℕ => (Numbering.decode n : ℕ)) :=
    by simpa using (Computable.id : Computable (fun n : ℕ ↦ n))
  have h0      := good?_code0 E
  have h1      := good?_code1 E
  exact
    Kleene.UCI.Classifier.uci (D := ℕ)
      Φ hC hDecode (good?_ext E) h0 h1

end CatTailUCI
