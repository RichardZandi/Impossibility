/-
Impossibility/Arrow/ArrowAxioms.lean
────────────────────────────────────
Axiom‑style definitions (no `sorry`) for Arrow’s voting conditions.
Depends only on `ArrowTypes.lean`.

* **UD**       Unrestricted domain (trivial for total functions)
* **Pareto**   If everyone prefers x to y, society does too.
* **IIA**      Pairwise independence.
* **Dictator** Agent whose strict preference always wins.
* **NonDict**  Negation of Dictator.
-/

import Impossibility.Arrow.ArrowTypes

open ArrowTypes

namespace ArrowAxioms

universe u

variable {α A : Type u}
variable [Fintype α] [DecidableEq α]
variable [Fintype A] [DecidableEq A]

/-- **Unrestricted domain** – every profile is admissible.  Since our
    social welfare function `F` is total on `Profile`, this is just `True`. -/
@[simp] def UD (F : Profile α A → SocialWelfare A) : Prop := True

/-- **Pareto efficiency** – unanimous strict preference lifts to society. -/
@[simp] def Pareto (F : Profile α A → SocialWelfare A) : Prop :=
  ∀ p x y, (∀ i, (p i).rel x y) → (F p).rel x y

/-- **Independence of irrelevant alternatives** – social ranking of
    `{x,y}` depends only on individual rankings of `{x,y}`. -/
@[simp] def IIA (F : Profile α A → SocialWelfare A) : Prop :=
  ∀ p q x y,
    (∀ i, (p i).rel x y ↔ (q i).rel x y) →
    ((F p).rel x y ↔ (F q).rel x y)

/-- **Dictatorship** – there exists an agent whose strict preference always
    determines the social strict preference. -/
@[simp] def Dictator (F : Profile α A → SocialWelfare A) : Prop :=
  ∃ i : α, ∀ p x y, (p i).rel x y → (F p).rel x y

/-- **Non‑dictatorship** – negation of `Dictator`. -/
@[simp] def NonDict (F : Profile α A → SocialWelfare A) : Prop := ¬ Dictator F

end ArrowAxioms
