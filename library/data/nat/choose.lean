/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.nat.choose
Authors: Leonardo de Moura

Choice function for decidable predicates on natural numbers.

This module provides the following two declarations:

choose      {p : nat → Prop} [d : decidable_pred p] : (∃ x, p x) → nat
choose_spec {p : nat → Prop} [d : decidable_pred p] (ex : ∃ x, p x) : p (choose ex)
-/
import data.subtype data.nat.basic data.nat.order
open nat subtype decidable well_founded

namespace nat
section find_x
parameter {p : nat → Prop}

private definition lbp (x : nat) : Prop := ∀ y, y < x → ¬ p y

private lemma lbp_zero : lbp 0 :=
λ y h, absurd h (not_lt_zero y)

private lemma lbp_succ {x : nat} : lbp x → ¬ p x → lbp (succ x) :=
λ lx npx y yltsx,
  or.elim (eq_or_lt_of_le yltsx)
    (λ yeqx, by rewrite [yeqx]; exact npx)
    (λ yltx, lx y yltx)

private definition gtb (a b : nat) : Prop :=
a > b ∧ lbp a

local infix `≺`:50 := gtb

private lemma acc_of_px {x : nat} : p x → acc gtb x :=
assume h,
acc.intro x (λ (y : nat) (l : y ≺ x),
  have h₁ : y > x,              from and.elim_left l,
  have h₂ : ∀ a, a < y → ¬ p a, from and.elim_right l,
  absurd h (h₂ x h₁))

private lemma acc_of_acc_succ {x : nat} : acc gtb (succ x) → acc gtb x :=
assume h,
acc.intro x (λ (y : nat) (l : y ≺ x),
   have ygtx  : x < y,    from and.elim_left l,
   by_cases
     (λ yeqx : y = succ x, by rewrite [yeqx]; exact h)
     (λ ynex : y ≠ succ x,
        have ygtsx : succ x < y, from lt_of_le_and_ne (succ_lt_succ ygtx) (ne.symm ynex),
        acc.inv h (and.intro ygtsx (and.elim_right l))))

private lemma acc_of_px_of_gt {x y : nat} : p x → y > x → acc gtb y :=
assume px ygtx,
acc.intro y (λ (z : nat) (l : z ≺ y),
  have zgty : z > y,              from and.elim_left l,
  have h    : ∀ a, a < z → ¬ p a, from and.elim_right l,
  absurd px (h x (lt.trans ygtx zgty)))

private lemma acc_of_acc_of_lt : ∀ {x y : nat}, acc gtb x → y < x → acc gtb y
| 0        y a0  ylt0  := absurd ylt0 !not_lt_zero
| (succ x) y asx yltsx :=
  assert ax : acc gtb x, from acc_of_acc_succ asx,
  by_cases
     (λ yeqx : y = x, by rewrite [yeqx]; exact ax)
     (λ ynex : y ≠ x, acc_of_acc_of_lt ax (lt_of_le_and_ne yltsx ynex))

parameter (ex : ∃ a, p a)
parameter [dp : decidable_pred p]
include dp

private lemma acc_of_ex (x : nat) : acc gtb x :=
obtain (w : nat) (pw : p w), from ex,
lt.by_cases
  (λ xltw : x < w, acc_of_acc_of_lt (acc_of_px pw) xltw)
  (λ xeqw : x = w, by rewrite [xeqw]; exact (acc_of_px pw))
  (λ xgtw : x > w, acc_of_px_of_gt pw xgtw)

private lemma wf_gtb : well_founded gtb :=
well_founded.intro acc_of_ex

private definition find.F (x : nat) : (Π x₁, x₁ ≺ x → lbp x₁ → {a : nat | p a}) → lbp x → {a : nat | p a} :=
match x with
| 0 := λ f l0, by_cases
  (λ p0 : p 0,    tag 0 p0)
  (λ np0 : ¬ p 0,
    have l₁ : lbp 1, from lbp_succ l0 np0,
    have g  : 1 ≺ 0, from and.intro (lt.base 0) l₁,
    f 1 g l₁)
| (succ n) := λ f lsn, by_cases
  (λ psn : p (succ n), tag (succ n) psn)
  (λ npsn : ¬ p (succ n),
    have lss : lbp (succ (succ n)), from lbp_succ lsn npsn,
    have g   : succ (succ n) ≺ succ n, from and.intro (lt.base (succ n)) lss,
    f (succ (succ n)) g lss)
end

private definition find_x : {x : nat | p x} :=
@fix _ _ _ wf_gtb find.F 0 lbp_zero
end find_x

protected definition choose {p : nat → Prop} [d : decidable_pred p] : (∃ x, p x) → nat :=
assume h, elt_of (find_x h)

protected theorem choose_spec {p : nat → Prop} [d : decidable_pred p] (ex : ∃ x, p x) : p (nat.choose ex) :=
has_property (find_x ex)
end nat
