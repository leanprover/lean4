/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Elegant pairing function.
-/
import data.nat.sqrt data.nat.div
open prod decidable
open - [notations] algebra

namespace nat
definition mkpair (a b : nat) : nat :=
if a < b then b*b + a else a*a + a + b

definition unpair (n : nat) : nat × nat :=
let s := sqrt n in
if n - s*s < s then (n - s*s, s) else (s, n - s*s - s)

theorem mkpair_unpair (n : nat) : mkpair (pr1 (unpair n)) (pr2 (unpair n)) = n :=
let s := sqrt n in
by_cases
  (suppose n - s*s < s,
    begin
      esimp [unpair],
      rewrite [if_pos this],
      esimp [mkpair],
      rewrite [if_pos this, add_sub_of_le (sqrt_lower n)]
    end)
  (suppose h₁ : ¬ n - s*s < s,
    have   s ≤ n - s*s,                  from le_of_not_gt h₁,
    assert s + s*s ≤ n - s*s + s*s,      from add_le_add_right this (s*s),
    assert s*s + s ≤ n,                  by rewrite [sub_add_cancel (sqrt_lower n) at this, add.comm at this]; assumption,
    have   n ≤ s*s + s + s,              from sqrt_upper n,
    have   n - s*s ≤ s + s,              from calc
        n - s*s ≤ (s*s + s + s) - s*s    : sub_le_sub_right this (s*s)
            ... = (s*s + (s+s)) - s*s    : by rewrite add.assoc
            ... = s + s                  : by rewrite add_sub_cancel_left,
    have   n - s*s - s ≤ s,              from calc
        n - s*s - s ≤ (s + s) - s        : sub_le_sub_right this s
                ... = s                  : by rewrite add_sub_cancel_left,
    assert h₂ : ¬ s < n - s*s - s,       from not_lt_of_ge this,
    begin
      esimp [unpair],
      rewrite [if_neg h₁], esimp,
      esimp [mkpair],
      rewrite [if_neg h₂, sub_sub, add_sub_of_le `s*s + s ≤ n`],
    end)

theorem unpair_mkpair (a b : nat) : unpair (mkpair a b) = (a, b) :=
by_cases
 (suppose a < b,
  assert a ≤ b + b, from calc
    a   ≤ b   : le_of_lt this
    ... ≤ b+b : !le_add_right,
  begin
    esimp [mkpair],
    rewrite [if_pos `a < b`],
    esimp [unpair],
    rewrite [sqrt_offset_eq `a ≤ b + b`, add_sub_cancel_left, if_pos `a < b`]
  end)
 (suppose ¬ a < b,
  have   b ≤ a,           from le_of_not_gt this,
  assert a + b ≤ a + a,   from add_le_add_left this a,
  have   a + b ≥ a,       from !le_add_right,
  assert ¬ a + b < a,     from not_lt_of_ge this,
  begin
    esimp [mkpair],
    rewrite [if_neg `¬ a < b`],
    esimp [unpair],
    rewrite [add.assoc (a * a) a b, sqrt_offset_eq `a + b ≤ a + a`, *add_sub_cancel_left, if_neg `¬ a + b < a`]
  end)

open prod.ops

theorem unpair_lt_aux {n : nat} : n ≥ 1 → (unpair n).1 < n :=
suppose n ≥ 1,
or.elim (eq_or_lt_of_le this)
  (suppose 1 = n, by subst n; exact dec_trivial)
  (suppose n > 1,
   let s := sqrt n in
   by_cases
    (suppose h : n - s*s < s,
      assert n > 0, from lt_of_succ_lt `n > 1`,
      assert sqrt n > 0, from sqrt_pos_of_pos this,
      assert sqrt n * sqrt n > 0, from mul_pos this this,
      begin unfold unpair, rewrite [if_pos h], esimp, exact sub_lt `n > 0` `sqrt n * sqrt n > 0` end)
    (suppose ¬ n - s*s < s, begin unfold unpair, rewrite [if_neg this], esimp, apply sqrt_lt `n > 1` end))

theorem unpair_lt : ∀ (n : nat), (unpair n).1 < succ n
| 0        := dec_trivial
| (succ n) :=
  have (unpair (succ n)).1 < succ n, from unpair_lt_aux dec_trivial,
  lt.step this
end nat
