/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.nat.comm_semiring
Author: Jeremy Avigad

ℕ is a comm_semiring.
-/
import data.nat.basic algebra.binary algebra.ring
open binary

namespace nat
section
  open [classes] algebra

  protected definition comm_semiring [instance] [reducible] : algebra.comm_semiring nat :=
  algebra.comm_semiring.mk add add.assoc zero zero_add add_zero add.comm
    mul mul.assoc (succ zero) one_mul mul_one mul.left_distrib mul.right_distrib
    zero_mul mul_zero (ne.symm (succ_ne_zero zero)) mul.comm
end

section port_algebra
  theorem mul.left_comm : ∀a b c : ℕ, a * (b * c) = b * (a * c) := algebra.mul.left_comm
  theorem mul.right_comm : ∀a b c : ℕ, (a * b) * c = (a * c) * b := algebra.mul.right_comm

  definition dvd (a b : ℕ) : Prop := algebra.dvd a b
  infix `|` := dvd
  theorem dvd.intro : ∀{a b c : ℕ} (H : a * c = b), a | b := @algebra.dvd.intro _ _
  theorem dvd.intro_left : ∀{a b c : ℕ} (H : c * a = b), a | b := @algebra.dvd.intro_left _ _
  theorem exists_eq_mul_right_of_dvd : ∀{a b : ℕ} (H : a | b), ∃c, b = a * c :=
    @algebra.exists_eq_mul_right_of_dvd _ _
  theorem dvd.elim : ∀{P : Prop} {a b : ℕ} (H₁ : a | b) (H₂ : ∀c, b = a * c → P), P :=
    @algebra.dvd.elim _ _
  theorem exists_eq_mul_left_of_dvd : ∀{a b : ℕ} (H : a | b), ∃c, b = c * a :=
    @algebra.exists_eq_mul_left_of_dvd _ _
  theorem dvd.elim_left : ∀{P : Prop} {a b : ℕ} (H₁ : a | b) (H₂ : ∀c, b = c * a → P), P :=
    @algebra.dvd.elim_left _ _
  theorem dvd.refl : ∀a : ℕ, a | a := algebra.dvd.refl
  theorem dvd.trans : ∀{a b c : ℕ} (H₁ : a | b) (H₂ : b | c), a | c := @algebra.dvd.trans _ _
  theorem eq_zero_of_zero_dvd : ∀{a : ℕ} (H : 0 | a), a = 0 := @algebra.eq_zero_of_zero_dvd _ _
  theorem dvd_zero : ∀a : ℕ, a | 0 := algebra.dvd_zero
  theorem one_dvd : ∀a : ℕ, 1 | a := algebra.one_dvd
  theorem dvd_mul_right : ∀a b : ℕ, a | a * b := algebra.dvd_mul_right
  theorem dvd_mul_left : ∀a b : ℕ, a | b * a := algebra.dvd_mul_left
  theorem dvd_mul_of_dvd_left : ∀{a b : ℕ} (H : a | b) (c : ℕ), a | b * c :=
    @algebra.dvd_mul_of_dvd_left _ _
  theorem dvd_mul_of_dvd_right : ∀{a b : ℕ} (H : a | b) (c : ℕ), a | c * b :=
    @algebra.dvd_mul_of_dvd_right _ _
  theorem mul_dvd_mul : ∀{a b c d : ℕ}, a | b → c | d → a * c | b * d :=
    @algebra.mul_dvd_mul _ _
  theorem dvd_of_mul_right_dvd : ∀{a b c : ℕ}, a * b | c → a | c :=
    @algebra.dvd_of_mul_right_dvd _ _
  theorem dvd_of_mul_left_dvd : ∀{a b c : ℕ}, a * b | c → b | c :=
    @algebra.dvd_of_mul_left_dvd _ _
  theorem dvd_add : ∀{a b c : ℕ}, a | b → a | c → a | b + c := @algebra.dvd_add _ _
end port_algebra
end nat
