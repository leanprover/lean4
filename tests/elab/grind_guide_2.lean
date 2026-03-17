
/-
New features since last `grind_guide.lean`
-/
set_option warn.sorry false
open Lean Grind Std

/-!
Complete procedure for linear integer arithmetic
-/
example (x y : Int) :
    27 ≤ 11*x + 13*y →
    11*x + 13*y ≤ 45 →
    -10 ≤ 7*x - 9*y →
    7*x - 9*y ≤ 4 → False := by
  grind

/-!
The linear integer arithmetic module is parametrized by the `ToInt` type classes.

Optimized `Nat` encoding (this quarter).
-/
#check ToInt

example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind

example (a b : Fin 15) : a = 0 → b = 1 → a + b > 2 → False := by
  grind

/-!
The commutative ring module is parametrized by several type classes
`CommRing`, `Ring`, `CommSemiring`, `Semiring`, `Field`,
`AddRightCancel`, `NoNatZeroDivisors`, `IsCharP`
-/
example [CommRing α] (a b c : α)
  : a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    a^4 + b^4 + c^4 = 9 := by
  grobner

example (x : BitVec 8) : (x + 16)*(x - 16) = x^2 := by
  grind

/-!
The linear arithmetic module supports `IntModule`, `CommRing`, etc.
-/

-- **Note**: It is just a preorder.
example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (a b c d e : α) :
    2*a + b ≥ 1 → b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0
    → a ≥ 3*c → c ≥ 6*e → d - e*5 ≥ 0
    → a + b + 3*c + d + 2*e < 0 → False := by
  grind

example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (f : α → α) (x : α)
    : Zero.zero ≤ x → x ≤ 0 → f x = a → f 0 = a := by
  grind

/-!
**Several new features implemented this quarter.**

Performance improvements: normalization, canonicalization, proof generation,
proof trimming, etc.
2.5x faster
-/

open Linarith in
set_option trace.grind.debug.proof true in -- Context should contain only `f 2` and `One`
example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (f : Nat → α) :
    f 1 <= 0 → f 2 <= 0 → f 3 <= 0 → f 4 <= 0 → f 5 <= 0 → f 6 <= 0 → f 7 <= 0 → f 8 <= 0 → -1 * f 2 + 1 <= 0 → False := by
  grind -order

/-!
Implemented support for `NatModule`
-/
section
variable (M : Type) [NatModule M]

example [AddRightCancel M] (x y : M) : 2 • x + 3 • y + x = 3 • (x + y) := by
  grind

example [LE M] [LT M] [LawfulOrderLT M] [IsLinearOrder M] [OrderedAdd M] {x y : M}
    : x ≤ y → 2 • x + y ≤ 3 • y := by
  grind
end

/-!
Implemented normalizers for non-commutative rings and semirings.
-/
example (R : Type u) [Ring R] (a b : R)
    : (a - 2 * b)^2 = a^2 - 2 * a * b - 2 * b * a + 4 * b^2 := by
  grind

example (R : Type u) [Semiring R] (a b : R)
    : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by
  grind

/-!
Implemented AC solver.
It is parametrized by the type classes Associative, Commutative, IsLawfulIdentity, IdempotentOp
-/

example {α} (op : α → α → α) [Associative op] (a b c d : α)
   : op a b = c →
     op b a = d →
     op (op c a) (op b c) = op (op a d) (op d b) := by
  grind

example {α β : Sort u} (bar : α → β) (op : α → α → α)
    [Associative op] [IdempotentOp op] (a b c d e f x y w : α)
    : op d (op x c) = op a b →
      op e (op f (op y w)) = op (op d a) (op b c) →
      bar (op d (op x c)) = bar (op e (op f (op y w))) := by
  grind only

/-!
Implemented support for "symbolic" `Fin` and `BitVec`
-/

example (p d : Nat) (n : Fin (p + 1))
    : 2 ≤ p → p ≤ d + 1 → d = 1 → n = 0 ∨ n = 1 ∨ n = 2 := by
  grind

example {n m : Nat} (x : BitVec n)
    : 2 ≤ n → n ≤ m → m = 2 → x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  grind

/-!
Implemented bridge between linear and nonlinear solvers.
-/

example (h : s = 4) : 4 < s - 1 + (s - 1) * (s - 1 - 1) / 2 := by
  grind

example (a : Nat) (ha : a < 8) (b c : Nat)
    : 2 ≤ b → c = 1 → b ≤ c + 1 → a * b < 8 * b := by
  grind

/-!
Generalized offset module: `grind order`.
- Support for `Ring` offset constraints (e.g., `x ≤ y + k`)
- Support for any type that implements at least a preorder. (**Extra**)
It is a forward reasoning solver, and computes the transitive closure of this kind of constraint.
It minimizes the number of case splits.
-/

example [LE α] [IsPreorder α]
    (a b c : α) : a ≤ b → b ≤ c → a ≤ c := by
  grind

example (a b : Int) (h : a + b > 5) : (if a + b ≤ 0 then b else a) = a := by
  grind -linarith -lia (splits := 0)

example [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) : a ≤ 5 → b ≤ 8 → a > 6 ∨ b > 10 → False := by
  grind -linarith (splits := 0)

example [LE α] [IsPartialOrder α]
    (a b c : α) : a ≤ b → b ≤ c → c ≤ a → a = c := by
  grind -linarith

example [LE α] [Std.IsLinearPreorder α]
    (a b c d : α) : a ≤ b → ¬ (c ≤ b) → ¬ (d ≤ c) → ¬ (a ≤ d) → False := by
  grind -linarith (splits := 0)

/-!
Implemented support injective functions. (**Extra**)
-/

structure InjFn (α : Type) (β : Type) where
  f : α → β
  h : Function.Injective f

instance : CoeFun (InjFn α β) (fun _ => α → β) where
  coe s := s.f

@[grind inj] theorem fn_inj (F : InjFn α β) : Function.Injective (F : α → β) := by
  grind [Function.Injective, cases InjFn]

def toList (a : α) : List α := [a]

@[grind inj] theorem toList_inj : Function.Injective (toList : α → List α) := by
  grind [Function.Injective, toList]

def succ (x : Nat) := x+1

@[grind inj] theorem succ_inj : Function.Injective succ := by
  grind [Function.Injective, succ]

example (F : InjFn α Nat) : toList (succ (F x)) = a → a = toList (succ (F y)) → x = y := by
  grind

/-!
Code actions for `grind` attributes and revised modifier semantics. (**Extra**)
Updated and documented all modifiers.

`!` modifier for enabling the "minimal indexable subexpression" condition.
-/

opaque p : Nat → Prop
opaque f : Nat → Nat
opaque r : Nat → Nat → Nat

@[grind] theorem rf_eq : p (f x) → r x (f y) = y := sorry

/-!
Improved diagnostics based on feedback by Bhavik (**Extra**)
-/

example {xs : List α} {i : Nat} (h : i < xs.length) :
    xs.take i ++ xs[i] :: xs.drop (i+1) = ys := by
  apply List.ext_getElem
  next => sorry
  next => sorry -- grind

/-!
Implemented solver plugin API (**Extra**)

See: `Order.lean`
-/

/-!
Annotation analyzer (**Extra**)
It will become a new command next quarter.
-/

/-
Next quarter:
- AC E-matching
- ungrind: `grind` tactic mode.

example : ...  := by
  grind => -- Enters `grind` tactic mode like we have for `conv`.
    -- When we hover terms and facts in the Info View we get see the anchors ;:
    --   #f124 : ∀ {a b c}, lt b a = false → lt c b = false → lt c a = false
    --   #d0a9 : lt xs[j] xs[i] = false → lt xs[i] xs[i] = false
    --   #p7ce : lt xs[j] xs[i] = true ∨ j ≤ i

    -- Attach a multi-pattern to the transitivity lemma (by anchor)
    pattern #f124 => lt  b a = false, lt c b = false

    -- Instantiate two useful ∀-facts (arguments may be anchors or terms)
    instantiate #f124 xs[i] xs[j] xs[i]

    -- Case split on a propositional disjunction, name the new hypotheses
    cases #p7ce with hLt hLe
    next => lia -- close the goal using cutsat
    next => finalize -- close the goal using the current search strategy used in `grind`
-/
