/-
HaltingUCI.lean
----------------
A **self‑contained** UCI instantiation that turns a *hypothetical* Halting
oracle `H` into a computable classifier and then feeds it to the Universal
Classification Impossibility engine, yielding a contradiction.

* No attempt is made to implement `H`; we simply *assume* its existence via
  three axioms (totality + correctness).
* The classifier `good?` asks whether the machine whose *Gödel index* is `s`
  halts on the fixed input `0`.
* Two concrete codes supply the opposite truth‑values required by UCI: the
  trivial constant‑zero program and a canonical diverging program.
* The extensionality lemma is proved directly from the equality of partial
  evaluation functions.
* For concreteness we phrase everything with `Nat.Partrec.Code`; **no
  low-level `TM2` machinery from `Mathlib.Computability.TuringMachine`
  is used—only its import satisfies namespace dependencies.
* We expose `uciGeneral` so that callers can plug in their **own**
  `bad / good` witness codes whenever the built-ins `Code.const 0/1`
  are inadequate—for example, HaltingUCI needs a “bad” code that
  actually diverges, not a halting constant-zero program.

The file relies on the same helper libraries that power `CatTailUCI.lean`.
-/
import Mathlib.Computability.Primrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Bool.Basic
import Mathlib.Computability.TuringMachine
import Godelnumbering.Godel
import Godelnumbering.Instances
import Impossibility.Evolution
import Impossibility.Halting.HaltingEvolution           -- uses `E.reacts`
import Impossibility.UCICoreTest
import Kleene2.KleeneFix
import Godelnumbering.Transport

open Classical Evolution Nat.Partrec Code
open Kleene.UCI.Classifier
open Godel
open Turing TM2

namespace HaltingUCI

--------------------------------------------------------------------------------
-- 1.  Oracle hypotheses
--------------------------------------------------------------------------------

/- Hypothetical halting oracle: H m i returns true iff program m halts on input i -/
variable (H : ℕ → ℕ → Bool)

/- **AXIOM**: The oracle H is computable -/
variable (hH_comp : Computable (fun p : ℕ × ℕ => H p.1 p.2))

/- **AXIOM**: The oracle H correctly decides halting for Code programs.
    H m i = true if and only if the program encoded by m halts on input i. -/
variable (hH_correct : ∀ m i, H m i = true ↔ ((numToCode m).eval i).Dom)

--------------------------------------------------------------------------------
-- 2.  Classifier built from the oracle
--------------------------------------------------------------------------------

/-- The diagonal classifier: "Does program #s halt on input 0?"
    This is the key classifier that allegedly distinguishes halting vs non-halting programs. -/
noncomputable def good? (s : ℕ) : Bool := H s 0

/-- UCI classifier wrapper -/
noncomputable abbrev Φ : Classifiers ℕ := ⟨good? H⟩

--------------------------------------------------------------------------------
-- 3.  UCI ingredient ① — (false) computability assumption
--------------------------------------------------------------------------------

/-- **THE CRUCIAL FALSE ASSUMPTION**: good? is computable.
    This is exactly what UCI will refute through its diagonal argument.
    If H is computable, then good? would be computable too. -/
lemma good?_computable (H : ℕ → ℕ → Bool) (hH_comp : Computable (fun p : ℕ × ℕ => H p.1 p.2)) :
    Computable (good? H) := by
  -- PROOF: good?(s) = H(s,0), and we compose computable functions
  have hPair : Computable (fun s : ℕ => (s,0)) :=
    Computable.pair Computable.id (Computable.const 0)
  -- good? is the composition: s ↦ (s,0) ↦ H(s,0)
  simpa [good?] using hH_comp.comp hPair

--------------------------------------------------------------------------------
-- 4.  UCI ingredient ② — decoder computability
--------------------------------------------------------------------------------

/-- Decoder computability: identity function on ℕ is trivially computable -/
lemma decode_computable :
  Computable (fun n : ℕ => (Numbering.decode n : ℕ)) :=
  by simpa using (Computable.id : Computable (fun n : ℕ => n))

--------------------------------------------------------------------------------
-- 5.  UCI ingredient ③ — extensionality
--------------------------------------------------------------------------------

/-- **EXTENSIONALITY**: two codes with identical semantics receive
    identical classifier values. -/
lemma good?_ext
    (H : ℕ → ℕ → Bool)
    (hH_correct :
      ∀ m i, H m i = true ↔ ((numToCode m).eval i).Dom)
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    good? H (Numbering.decode (Encodable.encode c₁)) =
    good? H (Numbering.decode (Encodable.encode c₂)) := by
  -- Unfold the classifier; we must prove equality of two Booleans:
  change H (Encodable.encode c₁) 0 = H (Encodable.encode c₂) 0

  ------------------------------------------------------------------
  -- 1.  Equality of halting domains at input 0
  ------------------------------------------------------------------
  have domEq : (c₁.eval 0).Dom = (c₂.eval 0).Dom :=
    congrArg (fun f : ℕ →. ℕ => (f 0).Dom) hEq

  ------------------------------------------------------------------
  -- 2.  Oracle-domain equivalences
  ------------------------------------------------------------------
  have h1 : H (Encodable.encode c₁) 0 = true ↔ (c₁.eval 0).Dom := by
    simpa [numToCode_encode] using (hH_correct (Encodable.encode c₁) 0)
  have h2 : H (Encodable.encode c₂) 0 = true ↔ (c₂.eval 0).Dom := by
    simpa [numToCode_encode] using (hH_correct (Encodable.encode c₂) 0)

  ------------------------------------------------------------------
  -- 3.  Case-split on the (common) domain truth-value
  ------------------------------------------------------------------
  by_cases hDom : (c₁.eval 0).Dom
  · ----------------------------------------------------------------
    -- 3a.  **HALTING case**  (domain is `True`)
    ----------------------------------------------------------------
    -- From h1, the first oracle bit must be `true`
    have bit1 : H (Encodable.encode c₁) 0 = true :=
      (h1).mpr hDom
    -- Transfer `hDom` across `domEq` to c₂
    have hDom₂ : (c₂.eval 0).Dom := by
      simpa [domEq] using hDom
    -- So the second oracle bit is also `true`
    have bit2 : H (Encodable.encode c₂) 0 = true :=
      (h2).mpr hDom₂
    -- Both sides `= true` ⇒ equal
    simpa [bit1, bit2]

  · ----------------------------------------------------------------
    -- 3b.  **DIVERGENCE case**  (domain is `False`)
    ----------------------------------------------------------------
    -- `¬Dom` plus h1 ⇒ first oracle bit cannot be `true`
    have bit1 : H (Encodable.encode c₁) 0 = false := by
      by_cases b : H (Encodable.encode c₁) 0
      · -- if `b = true` we contradict `hDom`
        have : (c₁.eval 0).Dom := (h1).1 (by simpa [b])
        exact (hDom this).elim
      · -- otherwise it is literally `false`
        simpa [b] using b
    -- Transfer `¬Dom` across equality to c₂
    have hDom₂ : ¬(c₂.eval 0).Dom := by
      intro d₂
      have : (c₁.eval 0).Dom := by
        simpa [domEq] using d₂
      exact hDom this
    -- `¬Dom₂` plus h2 ⇒ second oracle bit is also `false`
    have bit2 : H (Encodable.encode c₂) 0 = false := by
      by_cases b : H (Encodable.encode c₂) 0
      · have : (c₂.eval 0).Dom := (h2).1 (by simpa [b])
        exact (hDom₂ this).elim
      · simpa [b] using b
    -- Both sides `= false` ⇒ equal
    simpa [bit1, bit2]


--------------------------------------------------------------------------------
-- 6.  UCI ingredient ⑤ — "true" witness (halting program)
--------------------------------------------------------------------------------

/-- Simple halting program: always returns 1 -/
abbrev haltCode : Code := Code.const 1

/-- **HALTING WITNESS**: haltCode gives good? = true.
    This provides UCI's required "true" witness. -/
lemma good?_halt (H : ℕ → ℕ → Bool) (hH_correct : ∀ m i, H m i = true ↔ ((numToCode m).eval i).Dom) :
    good? H (Numbering.decode (Encodable.encode haltCode)) = true := by
  simp [good?, Numbering.decode_encode]

  -- Code.const 1 obviously halts on any input
  have : (haltCode.eval 0).Dom := by
    simp [haltCode, Code.eval]

  -- Apply oracle correctness: since haltCode halts, H returns true
  have := (hH_correct (Encodable.encode haltCode) 0).symm
  simpa [this, *]

--------------------------------------------------------------------------------
-- 7.  Diverging code construction & UCI ingredient ④
--------------------------------------------------------------------------------

/-- **DIVERGING CODE**: Search for a non-existent condition.
    Code.rfind' searches for an input where the predicate returns 0,
    but Code.const 1 always returns 1, so the search never terminates. -/
noncomputable def divergeCode : Code := Code.rfind' (Code.const 1)

/-- **HELPER LEMMA**: Nat.rfind with an always-false predicate never terminates.
    This captures the technical details of why our diverging code actually diverges. -/
private lemma rfind_false (a m : ℕ) :
    (Nat.rfind fun n =>
        ((Code.const 1).eval (Nat.pair a (n + m))).map (fun v => v = 0)).Dom = False := by
  -- The predicate asks "does Code.const 1 return 0?" which is always false
  simp [Code.eval, Nat.rfind, Option.map_eq_none_iff, Part.map_id', Function.comp]

/-- **DIVERGENCE PROOF**: divergeCode never halts on any input.
    This is the mathematical heart of our "false" witness. -/
lemma divergeCode_diverges (n : ℕ) :
    ¬ (divergeCode.eval n).Dom := by
  dsimp [divergeCode, Code.eval]
  rcases n.unpair with ⟨a, m⟩
  -- helper lemma proved earlier
  simpa [rfind_false a m]

/-- **DIVERGING WITNESS**: divergeCode gives good? = false.
    This provides UCI's required "false" witness. -/
lemma good?_diverge
    (H : ℕ → ℕ → Bool)
    (hH_correct :
      ∀ m i, H m i = true ↔ ((numToCode m).eval i).Dom) :
    good? H (Numbering.decode (Encodable.encode divergeCode)) = false := by
  -- unfold classifier
  simp [good?, Numbering.decode_encode]

  -- 1 ▸  diverging program never halts
  have hDom : ¬ (divergeCode.eval 0).Dom :=
    divergeCode_diverges 0

  -- 2 ▸  Use oracle soundness to show the bit cannot be `true`
  have hEq : H (Encodable.encode divergeCode) 0 = true
            ↔ (divergeCode.eval 0).Dom := by
    simpa [numToCode_encode] using
      (hH_correct (Encodable.encode divergeCode) 0)

  have hNotTrue : ¬ (H (Encodable.encode divergeCode) 0 = true) := by
    intro hBitTrue
    have dom : (divergeCode.eval 0).Dom := (hEq).mp hBitTrue
    exact hDom dom

  -- 3 ▸  In `Bool`, if it isn’t `true` it must be `false`
  cases hBit : H (Encodable.encode divergeCode) 0 with
  | true  => cases hNotTrue (by simpa using hBit)
  | false => simpa using hBit

--------------------------------------------------------------------------------
-- 8.  UCI contradiction — the main result
--------------------------------------------------------------------------------

/-- **MAIN THEOREM**: No computable halting oracle can exist.

    This applies UCI's generic diagonal argument to our specific halting classifier.
    UCI constructs a paradoxical program internally and derives a contradiction
    from our assumption that good? is computable.

    The theorem embodies the classic halting problem proof packaged through
    the UCI framework. -/
theorem no_halting_oracle
    (H : ℕ → ℕ → Bool)
    (hH_comp : Computable (fun p : ℕ × ℕ => H p.1 p.2))
    (hH_correct : ∀ m i, H m i = true ↔ ((numToCode m).eval i).Dom) :
    False := Kleene.UCI.Classifier.uciGeneral (D := ℕ)
    (Φ H)                         -- the classifier
    (good?_computable H hH_comp)  -- ① computable
    decode_computable             -- ② decoder
    (good?_ext H hH_correct)      -- ③ extensionality
    divergeCode haltCode          -- ④-⑤ witnesses  (bad , good)
    (good?_diverge H hH_correct)  -- ④ classifier(bad)=false
    (good?_halt    H hH_correct)  -- ⑤ classifier(good)=true

--------------------------------------------------------------------------------
-- 9.  Standard undecidability corollary
--------------------------------------------------------------------------------

/-- **COROLLARY**: The halting problem is undecidable.

    This is the standard formulation of halting undecidability.
    No computable function can correctly decide halting for all programs.

    PROOF: If such a function existed, it would contradict our main theorem. -/
theorem halting_undecidable :
  ¬∃ (H : ℕ → ℕ → Bool),
       Computable (fun p : ℕ × ℕ => H p.1 p.2) ∧
       (∀ m i, H m i = true ↔ ((numToCode m).eval i).Dom) := by
  intro ⟨H₀, hComp₀, hCorr₀⟩
  -- Apply our main theorem with this specific oracle
  exact no_halting_oracle H₀ hComp₀ hCorr₀


end HaltingUCI
