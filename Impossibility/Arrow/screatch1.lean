/-!  ------------------------------------------------------------
     Good-code classifier for Arrow’s proof
     ------------------------------------------------------------ -/


open ArrowHelper  -- brings GoodCode namespace in

variable {σ ι} [DecidableEq σ] [Inhabited ι] (X : Finset σ)

/-- **①**  Boolean predicate on honest codes: run the code, then test Arrow’s
     `GoodRule` on the resulting social-choice rule.               -/
noncomputable def goodCodeRule? (idx : GoodCode) : Bool :=
  goodRule? X (fun P =>
    -- interpret the code on Gödel–encoded profiles; default = constTrue
    (Code.eval (Godel.numToCode idx.val) (Encodable.encode P)).getD constTrue)

/-- **②**  Both the predicate itself and the decoder are computable.          -/
lemma goodCodeRule?_computable :
    Computable (goodCodeRule? (σ:=σ) (ι:=ι) X) := by
  -- `Code.eval` and `getD` are computable; `goodRule?` is decidable → computable
  unfold goodCodeRule?
  exact (Computable.comp (f:=goodRule? X) (by
    simpa using Computable.id))                 -- Lean’s `simp` resolves it

lemma GoodCode.decode_computable :
    Computable GoodCode.decode := by
  -- `decode` is just an `if` on a decidable predicate → computable
  unfold GoodCode.decode
  simpa using Computable.if _ _ _

/-- **③**  Extensionality: equal codes give equal Booleans.                   -/
lemma goodCodeRule?_ext {c₁ c₂ : Code}
    (h : c₁ = c₂) :
    goodCodeRule? (σ:=σ) (ι:=ι) X ⟨Encodable.encode c₁, by
      simp [ArrowHelper.goodCode]⟩ =
    goodCodeRule? (σ:=σ) (ι:=ι) X ⟨Encodable.encode c₂, by
      simp [ArrowHelper.goodCode, h]⟩ := by
  simpa [h]

/-- **④**  Bad / good witnesses wrapped as honest codes.                      -/
def idxDict : GoodCode :=
  ⟨Encodable.encode dictCode, by
    dsimp [ArrowHelper.goodCode]; simp⟩

def idxPareto [DecidableEq σ] : GoodCode :=
  ⟨Encodable.encode paretoCode, by
    dsimp [ArrowHelper.goodCode]; simp⟩

/-!  ------------------------------------------------------------
     Updated `UCI_Arrow`
     ------------------------------------------------------------ -/
theorem UCI_Arrow
    [Inhabited σ] [DecidableEq σ] (X : Finset σ) :
    ¬ ∃ f : Rule σ ι, GoodRule f X := by
  have : False :=
    uci
      -- Φ
      (Φ    := { C := goodCodeRule? (σ:=σ) (ι:=ι) X })
      -- hypotheses
      (hC   := goodCodeRule?_computable (σ:=σ) (ι:=ι) X)
      (hDec := GoodCode.decode_computable)
      (hExt := by
        intro c₁ c₂ hEq
        simpa using goodCodeRule?_ext (σ:=σ) (ι:=ι) X hEq)
      (h0   := by
        -- dictator fails GoodRule
        simp [goodCodeRule?, dict_bad?, idxDict])
      (h1   := by
        -- Pareto rule fails GoodRule
        simp [goodCodeRule?, pareto_bad?, idxPareto])
  exact this




/-- `goodCode n` holds when `n` *is* the Gödel number of **some** `Code`.
    We phrase it as a Boolean equality so it lives in `Prop`. -/
def goodCode (n : ℕ) : Prop :=
  (decode (α := Code) n).isSome = true

/-- Subtype of *honest* codes. -/
def GoodCode : Type := { n : ℕ // goodCode n }

/-- A canonical good code: the Gödel number of `Code.const 0`. -/
def defaultGood : GoodCode := by
  have : goodCode (encode (Code.const 0)) := by
    dsimp [goodCode]; simp
  exact ⟨encode (Code.const 0), this⟩

namespace GoodCode

/-- Forgetful encoder – trivially injective. -/
def encode (g : GoodCode) : ℕ := g.val

/-- Total decoder: keep `n` if it’s good, otherwise fall back to `defaultGood`. -/
noncomputable def decode (n : ℕ) : GoodCode :=
  if h : goodCode n then ⟨n, h⟩ else defaultGood

lemma decode_encode (g : GoodCode) : decode (encode g) = g := by
  dsimp [encode, decode]
  simp [g.property]

/-- The required Gödel-numbering instance. -/
noncomputable instance : Godel.Numbering GoodCode where
  encode        := encode
  decode        := decode
  decode_encode := decode_encode

namespace Part

/-- `getD p d` returns the value inside `p` if it halts,
    otherwise the supplied default `d`. -/
noncomputable def getD {α} (p : Part α) (d : α) : α := by
  by_cases h : p.Dom
  · exact p.get h
  · exact d

@[simp] lemma getD_some {α} (a d : α) : getD (Part.some a) d = a := by
  simp [getD]

end Part
open Part


def goodCode (n : ℕ) : Prop :=
  (Encodable.decode (α := Code) n).isSome        -- a `Prop`, no “= true”

noncomputable instance : Encodable GoodCode where
  encode g := g.val
  decode n := by
    classical
    exact if h : goodCode n then some ⟨n, h⟩ else none
  encodek g := by
    -- `g.property : goodCode g.val` picks the `then` branch
    simp [encode, decode, g.property]


instance : DecidablePred goodCode := fun n ↦
  -- `Bool` coerces to `Prop`, so we can reuse its decidability
  inferInstance

noncomputable def goodCode_primrec : PrimrecPred goodCode := by
  --  decode : ℕ → Option Code   is primitive-recursive
  --  isSome : Option _ → Bool   is primitive-recursive
  dsimp [goodCode]
  exact (Primrec.option_isSome.comp (Primrec.decode (α := Code)))


noncomputable instance : Primcodable GoodCode :=
  Primcodable.subtype         -- predicate inferred from the target type
    goodCode_primrec          -- ← single required argument


lemma goodCodeRule?_computable
    {σ ι} [DecidableEq σ] (X : Finset σ) :
    Computable (goodCodeRule? (σ:=σ) (ι:=ι) X) := by
  unfold goodCodeRule?
  exact Computable.comp (f := goodRule? X) (by
    simpa using Computable.id)

end GoodCode
