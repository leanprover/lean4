/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Int.Order


/--
The notation typeclass for heterogeneous scalar multiplication.
This enables the notation `a • b : γ` where `a : α`, `b : β`.

It is assumed to represent a left action in some sense.
The notation `a • b` is augmented with a macro (below) to have it elaborate as a left action.
Only the `b` argument participates in the elaboration algorithm: the algorithm uses the type of `b`
when calculating the type of the surrounding arithmetic expression
and it tries to insert coercions into `b` to get some `b'`
such that `a • b'` has the same type as `b'`.
See the module documentation near the macro for more details.
-/
class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a • b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent, but it is intended to be used for left actions. -/
  hSMul : α → β → γ

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class SMul (M : Type u) (α : Type v) where
  /-- `a • b` computes the product of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  smul : M → α → α

@[inherit_doc] infixr:73 " • " => HSMul.hSMul

/-!
We have a macro to make `x • y` notation participate in the expression tree elaborator,
like other arithmetic expressions such as `+`, `*`, `/`, `^`, `=`, inequalities, etc.
The macro is using the `leftact%` elaborator introduced in
[this RFC](https://github.com/leanprover/lean4/issues/2854).

As a concrete example of the effect of this macro, consider
```lean
variable [Ring R] [AddCommMonoid M] [Module R M] (r : R) (N : Submodule R M) (m : M) (n : N)
#check m + r • n
```
Without the macro, the expression would elaborate as `m + ↑(r • n : ↑N) : M`.
With the macro, the expression elaborates as `m + r • (↑n : M) : M`.
To get the first interpretation, one can write `m + (r • n :)`.

Here is a quick review of the expression tree elaborator:
1. It builds up an expression tree of all the immediately accessible operations
   that are marked with `binop%`, `unop%`, `leftact%`, `rightact%`, `binrel%`, etc.
2. It elaborates every leaf term of this tree
   (without an expected type, so as if it were temporarily wrapped in `(... :)`).
3. Using the types of each elaborated leaf, it computes a supremum type they can all be
   coerced to, if such a supremum exists.
4. It inserts coercions around leaf terms wherever needed.

The hypothesis is that individual expression trees tend to be calculations with respect
to a single algebraic structure.

Note(kmill): If we were to remove `HSMul` and switch to using `SMul` directly,
then the expression tree elaborator would not be able to insert coercions within the right operand;
they would likely appear as `↑(x • y)` rather than `x • ↑y`, unlike other arithmetic operations.
-/

@[inherit_doc HSMul.hSMul]
macro_rules | `($x • $y) => `(leftact% HSMul.hSMul $x $y)

instance {α : Type u} [Mul α] : HSMul α α α where
  hSMul x y := x * y

class NatModule (M : Type u) extends Zero M, Add M, HSMul Nat M M where
  add_zero : ∀ a : M, a + 0 = a
  zero_add : ∀ a : M, 0 + a = a
  add_comm : ∀ a b : M, a + b = b + a
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  zero_smul : ∀ a : M, 0 • a = 0
  one_smul : ∀ a : M, 1 • a = a
  add_smul : ∀ n m : Nat, ∀ a : M, (n + m) • a = n • a + m • a
  smul_zero : ∀ n : Nat, n • (0 : M) = 0
  smul_add : ∀ n : Nat, ∀ a b : M, n • (a + b) = n • a + n • b
  mul_smul : ∀ n m : Nat, ∀ a : M, (n * m) • a = n • (m • a)

class IntModule (M : Type u) extends Zero M, Add M, Neg M, Sub M, HSMul Int M M where
  add_zero : ∀ a : M, a + 0 = a
  zero_add : ∀ a : M, 0 + a = a
  add_comm : ∀ a b : M, a + b = b + a
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  zero_smul : ∀ a : M, (0 : Int) • a = 0
  one_smul : ∀ a : M, (1 : Int) • a = a
  add_smul : ∀ n m : Int, ∀ a : M, (n + m) • a = n • a + m • a
  neg_smul : ∀ n : Int, ∀ a : M, (-n) • a = - (n • a)
  smul_zero : ∀ n : Int, n • (0 : M) = 0
  smul_add : ∀ n : Int, ∀ a b : M, n • (a + b) = n • a + n • b
  mul_smul : ∀ n m : Int, ∀ a : M, (n * m) • a = n • (m • a)
  neg_add_cancel : ∀ a : M, -a + a = 0
  sub_eq_add_neg : ∀ a b : M, a - b = a + -b

/--
We keep track of rational linear combinations as integer linear combinations,
but with the assurance that we can cancel the GCD of the coefficients.
-/
class RatModule (M : Type u) extends IntModule M where
  no_int_zero_divisors : ∀ (k : Int) (a : M), k ≠ 0 → k • a = 0 → a = 0

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

class IntModule.IsOrdered (M : Type u) [Preorder M] [IntModule M] where
  neg_le_iff : ∀ a b : M, -a ≤ b ↔ -b ≤ a
  neg_lt_iff : ∀ a b : M, -a < b ↔ -b < a
  add_lt_left : ∀ a b c : M, a < b → a + c < b + c
  add_lt_right : ∀ a b c : M, a < b → c + a < c + b
  smul_pos : ∀ (k : Int) (a : M), 0 < a → (0 < k ↔ 0 < k • a)
  smul_neg : ∀ (k : Int) (a : M), a < 0 → (0 < k ↔ k • a < 0)
  smul_nonneg : ∀ (k : Int) (a : M), 0 ≤ a → 0 ≤ k → 0 ≤ k • a
  smul_nonpos : ∀ (k : Int) (a : M), a ≤ 0 → 0 ≤ k → k • a ≤ 0
