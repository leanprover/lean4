/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.binary init.combinator init.meta.interactive

universe variable u

class semigroup (A : Type u) extends has_mul A :=
(mul_assoc : ∀ a b c : A, a * b * c = a * (b * c))

variables {A : Type u}

@[simp] lemma mul_assoc [semigroup A] : ∀ a b c : A, a * b * c = a * (b * c) :=
semigroup.mul_assoc

class comm_semigroup (A : Type u) extends semigroup A :=
(mul_comm : ∀ a b : A, a * b = b * a)

@[simp] lemma mul_comm [comm_semigroup A] : ∀ a b : A, a * b = b * a :=
comm_semigroup.mul_comm

@[simp] lemma mul_left_comm [comm_semigroup A] : ∀ a b c : A, a * (b * c) = b * (a * c) :=
left_comm mul mul_comm mul_assoc

class left_cancel_semigroup (A : Type u) extends semigroup A :=
(mul_left_cancel : ∀ a b c : A, a * b = a * c → b = c)

lemma mul_left_cancel [left_cancel_semigroup A] {a b c : A} : a * b = a * c → b = c :=
left_cancel_semigroup.mul_left_cancel a b c

class right_cancel_semigroup (A : Type u) extends semigroup A :=
(mul_right_cancel : ∀ a b c : A, a * b = c * b → a = c)

lemma mul_right_cancel [right_cancel_semigroup A] {a b c : A} : a * b = c * b → a = c :=
right_cancel_semigroup.mul_right_cancel a b c

class monoid (A : Type u) extends semigroup A, has_one A :=
(one_mul : ∀ a : A, 1 * a = a) (mul_one : ∀ a : A, a * 1 = a)

@[simp] lemma one_mul [monoid A] : ∀ a : A, 1 * a = a :=
monoid.one_mul

@[simp] lemma mul_one [monoid A] : ∀ a : A, a * 1 = a :=
monoid.mul_one

class comm_monoid (A : Type u) extends monoid A, comm_semigroup A

class group (A : Type u) extends monoid A, has_inv A :=
(mul_left_inv : ∀ a : A, a⁻¹ * a = 1)

@[simp] lemma mul_left_inv [group A] : ∀ a : A, a⁻¹ * a = 1 :=
group.mul_left_inv

class comm_group (A : Type u) extends group A, comm_monoid A
