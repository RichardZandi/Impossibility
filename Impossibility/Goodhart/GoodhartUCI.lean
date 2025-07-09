import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec
import Mathlib.Data.Bool.Basic
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances
import Kleene2.KleeneFix
import Impossibility.UCICoreTest
import Mathlib.Tactic

open Classical
open Nat.Partrec Code
open Godel
open Kleene
open Kleene.UCI.Classifier

namespace GoodhartUCI

structure Classifiers (D : Type) where
  C : D → Bool

private def code0 : Code := Code.const 0
private def code1 : Code := Code.const 1

lemma uciGeneral
    {D : Type} [Numbering D] [Primcodable D]
    (Φ        : Classifiers D)
    (hC       : Computable Φ.C)
    (hDec     : Computable (fun n : ℕ => (Numbering.decode n : D)))
    (hExt     : ∀ {c₁ c₂ : Code},
                 c₁.eval = c₂.eval →
                 Φ.C (Numbering.decode (Encodable.encode c₁)) =
                 Φ.C (Numbering.decode (Encodable.encode c₂)))
    (bad good : Code)
    (hBad  : Φ.C (Numbering.decode (Encodable.encode bad))  = false)
    (hGood : Φ.C (Numbering.decode (Encodable.encode good)) = true) :
    False := by
  classical
  have hBit : Computable (fun c : Code =>
      Φ.C (Numbering.decode (Encodable.encode c))) := by
    exact hC.comp ((hDec.comp Computable.encode))
  have hSel : Computable (fun b : Bool => if b then bad else good) := by
    simpa using ((Primrec.ite (by
      dsimp [PrimrecPred]
      simpa using (Primrec.id : Primrec (fun b : Bool => b)))
      (Primrec.const bad) (Primrec.const good)).to_comp)
  let f : Code → Code :=
    fun c => if Φ.C (Numbering.decode (Encodable.encode c)) then bad else good
  have hf : Computable f := by
    simpa [f] using hSel.comp hBit
  rcases kleene_fix hf with ⟨c₀, hc⟩
  let d : D := Numbering.decode (Encodable.encode c₀)
  have hΦ_eq :
      Φ.C d = Φ.C (Numbering.decode (Encodable.encode (f c₀))) := by
    dsimp [d]; exact hExt hc
  cases hCd : Φ.C d with
  | false =>
      have hf₀ : f c₀ = good := by
        simp [f, d, hCd]
      have : (false : Bool) =
          Φ.C (Numbering.decode (Encodable.encode good)) := by
        simpa [hf₀, hCd] using hΦ_eq
      simpa [hGood] using this
  | true =>
      have hf₀ : f c₀ = bad := by
        simp [f, d, hCd]
      have : (true : Bool) =
          Φ.C (Numbering.decode (Encodable.encode bad)) := by
        simpa [hf₀, hCd] using hΦ_eq
      simpa [hBad] using this

theorem goodhart :
  ¬ ∃ Φ : Classifiers ℕ,
      Computable Φ.C ∧
      (∀ {c₁ c₂ : Code},
         c₁.eval = c₂.eval →
         Φ.C (Numbering.decode (Encodable.encode c₁)) =
         Φ.C (Numbering.decode (Encodable.encode c₂))) ∧
      Φ.C (Numbering.decode (Encodable.encode code0)) = false ∧
      Φ.C (Numbering.decode (Encodable.encode code1)) = true
:= by
  rintro ⟨Φ, hC, hExt, h0, h1⟩
  have hDec : Computable (fun n : ℕ => (Numbering.decode n : ℕ)) := by
    simpa using (Computable.id : Computable (fun n : ℕ => n))
  exact
    uciGeneral Φ hC hDec
               (by
                 intro c₁ c₂ h; exact hExt h)
               code0 code1 h0 h1

end GoodhartUCI
