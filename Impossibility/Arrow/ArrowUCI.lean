import Impossibility.Arrow.ArrowHelper
import Impossibility.UCICoreTest
import Kleene2.KleeneFix

open Classical MeasureTheory Set Kleene.UCI.Classifier
open ArrowTypes

universe u

variable {A : Type u} [Fintype A] [DecidableEq A]

/-- The UCI classifier built from the social‐welfare rule `F̂` with finite‐info bound `k`. -/
abbrev Φ : Classifier Ω (SocialWelfare A) := ⟨F̂, k, F_extensionality⟩

/-- Main theorem: no finite‐dependence aggregation rule can satisfy Pareto + IIA without dictatorship. -/
theorem no_arrow_rule : False :=
  uciGeneral
    (Φ := Φ)
    F_computable             -- ① classifier computable (or continuous)
    decode_computable        -- ② decoder computability
    (fun p q h => F_extensionality h)  -- ③ extensionality via prefix agreement
    bad good                 -- ④-⑤ witnesses: false‐profile then true‐profile
    bad_in_E                 -- classifier(bad) = false (bad ∈ E)
    good_in_notE             -- classifier(good) = true  (good ∉ E)

#exit
