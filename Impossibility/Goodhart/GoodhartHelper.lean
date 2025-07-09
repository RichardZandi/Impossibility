import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec
import Mathlib.Data.Bool.Basic
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances
import Kleene2.KleeneFix
import Impossibility.UCICoreTest
import Mathlib.Tactic
import Mathlib.Data.Nat.Pairing
import Mathlib.Computability.Partrec

open Classical
open Nat
open Nat.Partrec Code
open Godel
open Kleene
open Kleene.UCI.Classifier

/------------------------------------------------
  1.  System type and Gödel numbering
-------------------------------------------------/
structure Sys where
  metricCode : ℕ
  goalCode   : ℕ
  agentCode  : ℕ
deriving DecidableEq

def encodeSys : Sys → ℕ
| ⟨m, g, a⟩ => pair m (pair g a)

def decodeSys (n : ℕ) : Sys :=
  let ⟨m , t⟩ := unpair n
  let ⟨g , a⟩ := unpair t
  { metricCode := m, goalCode := g, agentCode := a }

lemma encode_decode (s : Sys) : decodeSys (encodeSys s) = s := by
  cases s with
  | mk m g a =>
      simp [encodeSys, decodeSys, unpair_pair]

instance : Encodable Sys where
  encode  := encodeSys
  decode  := fun n => some (decodeSys n)
  encodek := by
    intro s
    simp [encode_decode]

-- `Primcodable` follows from `Encodable`
-- put this near the `Sys` definition
open Primcodable

/-- `Sys` is equivalent to a triple `(ℕ × ℕ × ℕ)`, which already has
    both `Encodable` and `Primcodable` instances. -/
def tripleEquivSys : (ℕ × ℕ × ℕ) ≃ Sys where
  toFun   := fun t => ⟨t.1, t.2.1, t.2.2⟩
  invFun  := fun s => (s.metricCode, s.goalCode, s.agentCode)
  left_inv := by
    intro t; cases t with | mk m g => cases g; rfl
  right_inv := by
    intro s; cases s; rfl

/-- Inherit `Primcodable` for `Sys` from the triple via the equivalence. -/
instance : Primcodable Sys :=
  Primcodable.ofEquiv (α := ℕ × ℕ × ℕ) tripleEquivSys.symm


/------------------------------------------------
  2.  Faithfulness classifier
-------------------------------------------------/
def faithful? (s : Sys) : Bool := decide (s.metricCode = s.goalCode)

def faithfulNat (n : ℕ) : Bool := faithful? (decodeSys n)

lemma faithfulNat_computable : Computable faithfulNat := by
  -- turn the Primrec decoder into a Computable one
  have hDec   : Computable (fun n : ℕ => decodeSys n) :=
  (Computable.decode (α := Sys))

  -- 2.  Equality of natural numbers is computable, so this Boolean
  --     predicate on `Sys` values is computable.
  have hEq    : Computable (fun s : Sys => (s.metricCode == s.goalCode)) :=
    by
      -- projections are computable; so is `Nat.beq`
      simpa using
        ((Computable.beq.comp
            ((Computable.comp (Computable.const Sys.metricCode) Computable.id))
            ((Computable.comp (Computable.const Sys.goalCode)   Computable.id))))

  -- 3.  Compose the two pieces.
  have faithfulNat_computable : Computable faithfulNat := by
    -- faithfulNat n = (decodeSys n).metricCode == (decodeSys n).goalCode
    simpa [faithfulNat] using hEq.comp hDec


/------------------------------------------------
  3.  Behavioural extensionality
-------------------------------------------------/
def sameBehaviour (s₁ s₂ : Sys) : Prop :=
  s₁.metricCode = s₂.metricCode ∧
  s₁.goalCode   = s₂.goalCode   ∧
  s₁.agentCode  = s₂.agentCode

lemma faithful_ext {s₁ s₂ : Sys} (h : sameBehaviour s₁ s₂) :
    faithful? s₁ = faithful? s₂ := by
  cases s₁; cases s₂; rcases h with ⟨h1, h2, _⟩
  simp [faithful?, h1, h2]

/------------------------------------------------
  4.  Witness systems
-------------------------------------------------/
def goodSys : Sys := { metricCode := 0, goalCode := 0, agentCode := 0 }
def badSys  : Sys := { metricCode := 0, goalCode := 1, agentCode := 0 }

def good : Code := Code.const (encodeSys goodSys)
def bad  : Code := Code.const (encodeSys badSys)

lemma hGood : faithful? (decodeSys (encodeSys goodSys)) = true := by
  simp [faithful?, encodeSys, decodeSys]

lemma hBad  : faithful? (decodeSys (encodeSys badSys))  = false := by
  simp [faithful?, encodeSys, decodeSys]

/------------------------------------------------
  5.  Bundle classifier and invoke UCI engine
-------------------------------------------------/
structure Classifiers (D : Type) where
  C : D → Bool

def Φ : Classifiers ℕ := { C := faithfulNat }

lemma ext_code {c₁ c₂ : Code} (h : c₁.eval = c₂.eval) :
    Φ.C (Encodable.encode c₁) = Φ.C (Encodable.encode c₂) := by
  -- `faithfulNat` depends only on the numeric code, not on evaluation.
  simp [Φ, faithfulNat]

lemma goodhart_impossibility :
    False := by
  -- computable decoder for ℕ is identity
  have hDecℕ : Computable (fun n : ℕ => (n : ℕ)) := Computable.id
  exact
    Kleene.UCI.Classifier.uciGeneral
      Φ faithfulNat_computable hDecℕ (@ext_code)
      bad good hBad hGood
