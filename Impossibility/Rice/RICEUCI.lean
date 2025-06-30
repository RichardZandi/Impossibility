/-
RiceUCI.lean
────────────
A UCI-style proof of Rice’s Theorem:

    No computable total predicate can decide a
    non-trivial semantic property of partial-recursive
    functions (i.e. of `Code` programs).

We assume:
  • R : ℕ → Bool         – candidate decider
  • R is computable
  • R respects extensionality of `Code.eval`
  • R is *non-trivial*: there exist codes cT and cF
    s.t. R(encode cT) = true,  R(encode cF) = false

From these we obtain `False` via `uciGeneral`.
-/

import Impossibility.UCICoreTest
import Mathlib.Computability.PartrecCode
import Godelnumbering.Transport
import Godelnumbering.Godel
import Godelnumbering.Instances


open Classical Nat.Partrec Code Godel
open Kleene.UCI.Classifier

namespace RiceUCI

/-- constant program returning 1 – used as “positive” witness -/
abbrev cT : Code := Code.const 1

/-- constant program returning 0 – used as “negative” witness -/
abbrev cF : Code := Code.const 0

/-- decoder on ℕ is the identity, hence computable -/
def decode_comp : Computable (fun n : ℕ => (Numbering.decode n : ℕ)) :=
  by
    simpa using (Computable.id)

/-- lift extensionality through `Numbering.decode` (helper) -/
lemma extensional_lift
    (R : ℕ → Bool)
    (hR_ext :
      ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
        R (Encodable.encode c₁) = R (Encodable.encode c₂))
    {c₁ c₂ : Code} (hEq : c₁.eval = c₂.eval) :
    R (Numbering.decode (Encodable.encode c₁)) =
    R (Numbering.decode (Encodable.encode c₂)) := by
  simpa [Numbering.decode_encode] using (hR_ext hEq)

/-- Rice’s theorem: no computable total decider for a non-trivial
    semantic property of partial-recursive functions. -/
theorem no_semantic_decider
    (R       : ℕ → Bool)
    (hR_comp : Computable R)
    (hR_ext  : ∀ {c₁ c₂ : Code}, c₁.eval = c₂.eval →
                 R (Encodable.encode c₁) = R (Encodable.encode c₂))
    (hTrue  : R (Encodable.encode cT) = true)
    (hFalse : R (Encodable.encode cF) = false) :
    False := by
  -- bundle R as a classifier
  let Φ : Classifiers ℕ := ⟨R⟩
  -- apply the generic diagonal engine
  exact
    Kleene.UCI.Classifier.uciGeneral (D := ℕ)
      Φ
      hR_comp
      decode_comp
      (extensional_lift R hR_ext)
      cF cT
      (by
        simpa [Numbering.decode_encode] using hFalse)
      (by
        simpa [Numbering.decode_encode] using hTrue)

end RiceUCI
