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

structure Sys where
  metricCode : ℕ
  goalCode   : ℕ
  agentCode  : ℕ
deriving DecidableEq

def encodeSys : Sys → ℕ
| ⟨m,g,a⟩ => Nat.pair m (Nat.pair g a)

def decodeSys (n : ℕ) : Sys :=
  let ⟨m,t⟩ := Nat.unpair n
  let ⟨g,a⟩ := Nat.unpair t
  { metricCode := m, goalCode := g, agentCode := a }

lemma encode_decode (s : Sys) : decodeSys (encodeSys s) = s := by
  cases s <;> simp [encodeSys, decodeSys, unpair_pair]

instance : Encodable Sys where
  encode := encodeSys
  decode := fun n => some (decodeSys n)
  encodek := by intro s; simp [encode_decode]

instance : Numbering Sys :=
  ⟨encodeSys,decodeSys,by intro s; simp [encode_decode]⟩

def tripleEquivSys : (ℕ × ℕ × ℕ) ≃ Sys where
  toFun := fun t => ⟨t.1,t.2.1,t.2.2⟩
  invFun := fun s => (s.metricCode,s.goalCode,s.agentCode)
  left_inv := by intro t; cases t with | mk m g => cases g; rfl
  right_inv := by intro s; cases s; rfl

instance : Primcodable Sys :=
  Primcodable.ofEquiv (α:=ℕ×ℕ×ℕ) tripleEquivSys.symm

def faithful? (s : Sys) : Bool :=
  decide (s.metricCode = s.goalCode)

def goodSys : Sys := { metricCode:=0, goalCode:=0, agentCode:=0 }
def badSys  : Sys := { metricCode:=0, goalCode:=1, agentCode:=0 }

def good : Code := Code.const (encodeSys goodSys)
def bad  : Code := Code.const (encodeSys badSys)

def defaultCode : Code := Code.const 0

instance : Numbering Code where
  encode := fun c => Encodable.encode c
  decode := fun n => (Encodable.decode (α := Code) n).getD defaultCode
  decode_encode := by         -- use this field name
    intro c
    have h : Encodable.decode (α := Code) (Encodable.encode c) = some c := by
      simpa using Encodable.encodek c
    simp [h, defaultCode]


instance : Primcodable Code := inferInstance

def optionGetCode (o : Option Code) : Code :=
  o.getD defaultCode

lemma optionGetCode_computable : Computable optionGetCode := by
  have h₁ : Computable (fun o : Option Code => o) := Computable.id
  have h₂ : Computable (fun _ : Option Code => defaultCode) :=
    Computable.const defaultCode
  simpa using (Computable.option_getD (hf := h₁) (hg := h₂))

/- the ℕ → Code decoder that `uciGeneral` expects -/
def decCode (n : ℕ) : Code :=
  optionGetCode (Encodable.decode (α := Code) n)

lemma decCode_computable : Computable decCode := by
  have hDec : Computable (fun n : ℕ =>
      (Encodable.decode (α := Code) n : Option Code)) :=
    Computable.decode
  simpa [decCode] using optionGetCode_computable.comp hDec

lemma decodeCode_computable : Computable decCode :=
  decCode_computable

@[simp] lemma decode_encode_code (c : Code) :
    (Numbering.decode (Encodable.encode c) : Code) = c := by
  have h : Encodable.decode (α := Code) (Encodable.encode c) = some c := by
    simpa using Encodable.encodek c
  simp [Numbering.decode, defaultCode, h]


lemma goodhart_impossibility
    (Φ    : Classifiers Code)
    (hC   : Computable Φ.C)
    (hExt : ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval → Φ.C c₁ = Φ.C c₂)
    (hBad : Φ.C bad  = false)
    (hGood: Φ.C good = true) :
    False :=
  Kleene.UCI.Classifier.uciGeneral
    Φ
    hC
    decCode_computable
    (by
      intro c₁ c₂ h
      have h' : Φ.C c₁ = Φ.C c₂ := hExt h
      simpa [Numbering.decode_encode] using h')
    bad good
    (by
      simpa [Numbering.decode_encode] using hBad)
    (by
      simpa [Numbering.decode_encode] using hGood)
