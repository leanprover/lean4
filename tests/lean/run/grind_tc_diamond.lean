-- Adapted from https://github.com/marcusrossel/lean-egg

-- Inspired by:
-- Wieser, Eric. "Multiple-inheritance hazards in dependently-typed algebraic hierarchies."
-- International Conference on Intelligent Computer Mathematics.
-- Cham: Springer Nature Switzerland, 2023.

namespace Nested

class AddCommMonoid (α : Type _) where
  add : α → α → α
  zero : α
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a
  add_comm : ∀ a b : α, add a b = add b a

class AddCommGroup (α : Type _) extends AddCommMonoid α where
  neg : α → α
  add_neg : ∀ a : α, add (neg a) a = zero
  neg_add : ∀ a : α, add a (neg a) = zero

class Semiring (α : Type _) extends AddCommMonoid α where
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  one : α
  mul_one : ∀ a : α, mul a one = a
  one_mul : ∀ a : α, mul one a = a
  left_distrib : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)
  zero_mul : ∀ a : α, mul zero a = zero
  mul_zero : ∀ a : α, mul a zero = zero

class Ring (α : Type _) extends Semiring α, AddCommGroup α where

attribute [grind] AddCommMonoid.add_zero
attribute [grind] AddCommMonoid.zero_add
attribute [grind] AddCommMonoid.add_comm
attribute [grind] AddCommGroup.add_neg
attribute [grind] AddCommGroup.neg_add
attribute [grind] Semiring.mul_assoc
attribute [grind] Semiring.mul_one
attribute [grind] Semiring.one_mul
attribute [grind] Semiring.left_distrib
attribute [grind] Semiring.right_distrib
attribute [grind] Semiring.zero_mul
attribute [grind] Semiring.mul_zero

open AddCommMonoid AddCommGroup Semiring Ring

infixl:65 (priority := high) " + " => add
infixl:70 (priority := high) " * " => mul
prefix:75 (priority := high) "-"   => Ring.neg

theorem test [Ring α] (a b : α) : a + b = b + a := by
  grind

theorem just_nested [Ring α] (a : α) : (a + zero) * one = a := by
  grind

theorem combine_classes [Ring α] (a b c : α) (h : b + c = one) : (a + (b + -b)) * (b + c) = a := by
  grind -- Fails!

end Nested

namespace Flat

class Ring (α : Type _) where
  add : α → α → α
  zero : α
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a
  add_comm : ∀ a b : α, add a b = add b a
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  one : α
  mul_one : ∀ a : α, mul a one = a
  one_mul : ∀ a : α, mul one a = a
  left_distrib : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)
  zero_mul : ∀ a : α, mul zero a = zero
  mul_zero : ∀ a : α, mul a zero = zero
  neg : α → α
  add_neg : ∀ a : α, add (neg a) a = zero
  neg_add : ∀ a : α, add a (neg a) = zero

attribute [grind] Ring.add_zero
attribute [grind] Ring.zero_add
attribute [grind] Ring.add_comm
attribute [grind] Ring.add_neg
attribute [grind] Ring.neg_add
attribute [grind] Ring.mul_assoc
attribute [grind] Ring.mul_one
attribute [grind] Ring.one_mul
attribute [grind] Ring.left_distrib
attribute [grind] Ring.right_distrib
attribute [grind] Ring.zero_mul
attribute [grind] Ring.mul_zero

open Ring

infixl:65 (priority := high) " + " => add
infixl:70 (priority := high) " * " => mul
prefix:75 (priority := high) "-"   => neg

theorem test [Ring α] (a b : α) : a + b = b + a := by
  grind

theorem just_nested [Ring α] (a : α) : (a + zero) * one = a := by
  grind

theorem combine_classes [Ring α] (a b c : α) (h : b + c = one) : (a + (b + -b)) * (b + c) = a := by
  grind

end Flat
