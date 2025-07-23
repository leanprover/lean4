/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
module

prelude
public import Init.Core

public section

/-!
Instances converting between `Zero α` and `OfNat α (nat_lit 0)`.
-/

instance (priority := 300) Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

instance (priority := 200) Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0

/-!
Instances converting between `One α` and `OfNat α (nat_lit 1)`.
-/

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

/--
The fundamental power operation in a monoid.
`npowRec n a = a*a*...*a` n times.
This function should not be used directly; it is often used to implement a `Pow M Nat` instance,
but end users should use the `a ^ n` notation instead.
-/
@[expose]
def npowRec [One M] [Mul M] : Nat → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a

/--
The fundamental scalar multiplication in an additive monoid.
`nsmulRec n a = a+a+...+a` n times.
This function should not be used directly;
it is often used to implement an instance for scalar multiplication.
-/
def nsmulRec [Zero M] [Add M] : Nat → M → M
  | 0, _ => 0
  | n + 1, a => nsmulRec n a + a
