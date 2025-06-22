/-
PZIUCI.lean
-----------
A UCI instantiation that shows **no total computable *prefix* rule**
can decide the measure-zero escape set “never reaches 1’’ in the infinite
Collatz casino.  The total system dynamics come from `PZIEvolution.lean`;
we *assume* the existence of a computable Boolean predicate
`pref? : ℕ → Bool` reading only finitely many rounds, then feed it to
`uciGeneral` with the canonical witnesses
`bad = Code.const 1` (reaches 1 immediately)
`good = Code.const 0` (never reaches 1).
-/

import Mathlib.Computability.Primrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Bool.Basic
import Godelnumbering.Godel
import Godelnumbering.Instances
import Impossibility.Evolution
import Impossibility.PZI.PZIEvolution           -- brings `PZIE : Evolution`
import Impossibility.UCICoreTest               -- uciGeneral
import Kleene2.KleeneFix
import Godelnumbering.Transport

open Classical Nat.Partrec Code
open Kleene.UCI.Classifier
open Godel

namespace PZIUCI

--------------------------------------------------------------------------------
-- 1.  Prefix classifier (assumed computable)
--------------------------------------------------------------------------------

/-- `pref? s` claims whether the run starting from Gödel index `s`
    **never hits 1** (escape).  We *assume* it is total computable; UCI
    will refute that assumption.                                         -/
noncomputable def pref? (s : ℕ) : Bool :=
  decide (∀ k : ℕ, PZIE.F s k ≠ 1)


/- - **ASSUMPTION**: the prefix rule is computable.                     -/
variable (hPrefComp : Computable pref?)

noncomputable abbrev Φ : Classifiers ℕ := ⟨pref?⟩

--------------------------------------------------------------------------------
-- 2.  Decoder computability (identical to HaltingUCI)
--------------------------------------------------------------------------------

lemma decode_computable :
    Computable (fun n : ℕ => (Numbering.decode n : ℕ)) :=
  by simpa using (Computable.id : Computable fun n : ℕ => n)

--------------------------------------------------------------------------------
-- 3.  Extensionality  (uses `ExtensionalF` for PZIE)
--------------------------------------------------------------------------------

instance : ExtensionalF PZIE := inferInstance   -- from the file itself

lemma pref?_ext
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    pref? (Encodable.encode c₁) = pref? (Encodable.encode c₂) := by
  -- unfold `pref?`
  dsimp [pref?]
  -- extensional equality of `F` values follows from `PZIE.reacts`
  -- and the `ExtensionalF` instance
  have hF :
      ∀ k, PZIE.F (Encodable.encode c₁) k =
            PZIE.F (Encodable.encode c₂) k := by
    have := (ExtensionalF.ext (E := PZIE) hEq)
    simpa using this
  -- rewrite both decide-statements with `FunLike.ext`
  simp [hF]

--------------------------------------------------------------------------------
-- 4.  Witness codes
--------------------------------------------------------------------------------

/-- `bad` reaches 1 at step 0 → classifier must give **false**. -/
abbrev bad  : Code := Code.const 1
/-- `good` never reaches 1         → classifier must give **true**. -/
abbrev good : Code := Code.const 0

/-- `bad` reaches 1 immediately ⇒ the prefix classifier must say **false**. -/
lemma pref?_bad : pref? (Encodable.encode bad) = false := by
  classical
  -- expand the definition
  dsimp [pref?, bad]
  -- `F (encode bad) 0 = 1`: follows from `PZIE.reacts` and `eval_const`
  have h0 : PZIE.F (Encodable.encode (Code.const 1)) 0 = 1 := by
    have : (Code.const 1).eval 0 = pure 1 := by simp
    simpa using (PZIE.reacts this)
  -- therefore the quantified predicate is *not* true
  have hNot : ¬ (∀ k : ℕ, PZIE.F (Encodable.encode (Code.const 1)) k ≠ 1) := by
    intro hAll; have := hAll 0; simp [h0] at this
  -- `decide` of a false proposition is `false`
  simp [hNot]

/-- `good` is the constant-zero code ⇒ the classifier must say **true**. -/
lemma pref?_good : pref? (Encodable.encode good) = true := by
  classical
  dsimp [pref?, good]
  -- for every `k`, `F (encode good) k = 0`
  have hVal : ∀ k : ℕ, PZIE.F (Encodable.encode (Code.const 0)) k = 0 := by
    intro k
    have : (Code.const 0).eval k = pure 0 := by simp
    simpa using (PZIE.reacts this)
  -- hence the quantified predicate *is* true
  have hAll : (∀ k : ℕ, PZIE.F (Encodable.encode (Code.const 0)) k ≠ 1) := by
    intro k; have := hVal k; simp [this]
  -- `decide` of a true proposition is `true`
  simp [hAll]

--------------------------------------------------------------------------------
-- 5.  UCI contradiction
--------------------------------------------------------------------------------

theorem prefix_zero_set_impossible
    (hPrefComp : Computable pref?) :      -- ‹① computability slot›
    False :=
  Kleene.UCI.Classifier.uciGeneral
    (D := ℕ)
    Φ
    hPrefComp
    decode_computable
    (by
      intro c₁ c₂ h;                      -- ③ extensionality
      simpa using pref?_ext h)
    bad good                              -- ④ / ⑤ witnesses
    (by simpa using pref?_bad)            -- classifier bad = false
    (by simpa using pref?_good)           -- classifier good = true

end PZIUCI
