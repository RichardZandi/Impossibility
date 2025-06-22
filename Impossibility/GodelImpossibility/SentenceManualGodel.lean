import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Pairing
/-
SentenceManualNumberingGodel.lean
================================
Self‑contained syntax and Gödel numbering for a first‑order arithmetic
fragment strong enough for an incompleteness proof.  We *do not* index
formulas by the number of free variables—this bypasses Lean’s positivity
restriction that blocked the earlier `all`/`ex` constructors.

### Language summary
* **Term constructors**   `var n`, `0`, `succ`, `plus`, `times`
* **Atomic relations**   `eq`, `lt`
* **Connectives**       `⊥`, `¬`, `∧`, `∨`, `→`
* **Quantifiers**       `∀`, `∃`

Variable binding uses de Bruijn *levels*: a natural number `n : ℕ` in
`Term.var n` refers to the variable whose binder is `n` steps *away*.

Every constructor has a **numeric tag** (`Tag.*`) so that
`Sentence.encode` is primitive‑recursive and prefix‑decidable.
-/

namespace SentenceCode

abbrev Code := List ℕ

/- ### Numeric tags ------------------------------------------------------ -/
namespace Tag
  -- term layer
  def var   : ℕ := 1
  def c0    : ℕ := 2
  def succ  : ℕ := 3
  def plus  : ℕ := 4
  def times : ℕ := 5
  -- formula layer
  def eq_    : ℕ := 6
  def lt_    : ℕ := 7
  def falsum : ℕ := 8
  def not_   : ℕ := 9
  def and_   : ℕ := 10
  def or_    : ℕ := 11
  def imp_   : ℕ := 12
  def all_   : ℕ := 13
  def ex_    : ℕ := 14
end Tag
open Tag

/- ### Helpers ----------------------------------------------------------- -/
@[inline] def encNat (n : ℕ) : Code := List.replicate n 0 ++ [1]

/- ### Terms ------------------------------------------------------------- -/
/- ### Terms ------------------------------------------------------------- -/
/- We avoid name‑clashes with mathlib’s `Term` by calling the datatype
   `Tm`. -/
inductive Tm : Type
| var   (n : ℕ)   : Tm
| c0              : Tm
| succ  : Tm → Tm
| plus  : Tm → Tm → Tm
| times : Tm → Tm → Tm

deriving DecidableEq

namespace Tm
  @[simp] def encode : Tm → Code
  | var n        => [Tag.var]   ++ encNat n
  | c0           => [Tag.c0]
  | succ t       => [Tag.succ]  ++ encode t
  | plus t u     => [Tag.plus]  ++ encode t ++ encode u
  | times t u    => [Tag.times] ++ encode t ++ encode u
end Tm

/- ### Sentences --------------------------------------------------------- -/
inductive Sentence : Type
| falsum                         : Sentence
| eq   (t u : Tm)              : Sentence
| lt   (t u : Tm)              : Sentence
| not  (φ   : Sentence)          : Sentence
| and  (φ ψ : Sentence)          : Sentence
| or   (φ ψ : Sentence)          : Sentence
| imp  (φ ψ : Sentence)          : Sentence
| all  (φ   : Sentence)          : Sentence   -- ∀ binder (body φ)
| ex   (φ   : Sentence)          : Sentence   -- ∃ binder

deriving DecidableEq

namespace Sentence
  @[simp] def encode : Sentence → Code
  | falsum        => [Tag.falsum]
  | eq t u        => [Tag.eq_]   ++ Tm.encode t ++ Tm.encode u
  | lt t u        => [Tag.lt_]   ++ Tm.encode t ++ Tm.encode u
  | not φ         => [Tag.not_]  ++ encode φ
  | and φ ψ       => [Tag.and_]  ++ encode φ ++ encode ψ
  | or  φ ψ       => [Tag.or_]   ++ encode φ ++ encode ψ
  | imp φ ψ       => [Tag.imp_]  ++ encode φ ++ encode ψ
  | all φ         => [Tag.all_]  ++ encode φ
  | ex  φ         => [Tag.ex_]   ++ encode φ
end Sentence

/- ### Closed sentences (no free variables) ------------------------------ -/
/-  In a de Bruijn level convention, a *closed* term/sentence just means
   we keep track informally and never mention `var n` outside a quantifier.
   For Gödel coding we treat *all* sentences the same; closedness is a
   semantic property checked elsewhere. -/

abbrev ClosedSentence := Sentence

open Nat

@[inline] def codeToNat : Code → ℕ
| []      => 0
| n :: r  => Nat.pair n (codeToNat r)


end SentenceCode
