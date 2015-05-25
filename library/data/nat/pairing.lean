/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Elegant pairing function.
-/
import data.nat.sqrt data.nat.div
open prod decidable

namespace nat
definition mkpair (a b : nat) : nat :=
if a < b then b*b + a else a*a + a + b

definition unpair (n : nat) : nat × nat :=
let s := sqrt n in
if n - s*s < s then (n - s*s, s) else (s, n - s*s - s)

theorem mkpair_unpair (n : nat) : mkpair (pr1 (unpair n)) (pr2 (unpair n)) = n :=
let s := sqrt n in
by_cases
  (λ h₁ : n - s*s < s,
    begin
      esimp [unpair],
      rewrite [if_pos h₁],
      esimp [mkpair],
      rewrite [if_pos h₁, add_sub_of_le (sqrt_lower n)]
    end)
  (λ h₂ : ¬ n - s*s < s,
    have   g₁ : s ≤ n - s*s,             from le_of_not_gt h₂,
    assert g₂ : s + s*s ≤ n - s*s + s*s, from add_le_add_right g₁ (s*s),
    assert g₃ : s*s + s ≤ n,             by rewrite [sub_add_cancel (sqrt_lower n) at g₂, add.comm at g₂]; exact g₂,
    have l₁   : n ≤ s*s + s + s,         from sqrt_upper n,
    have l₂   : n - s*s ≤ s + s,         from calc
        n - s*s ≤ (s*s + s + s) - s*s    : sub_le_sub_right l₁ (s*s)
            ... = (s*s + (s+s)) - s*s    : by rewrite add.assoc
            ... = s + s                  : by rewrite add_sub_cancel_left,
    have l₃   : n - s*s - s ≤ s,         from calc
        n - s*s - s ≤ (s + s) - s        : sub_le_sub_right l₂ s
                ... = s                  : by rewrite add_sub_cancel_left,
    assert l₄ : ¬ s < n - s*s - s,       from not_lt_of_ge l₃,
    begin
      esimp [unpair],
      rewrite [if_neg h₂], esimp,
      esimp [mkpair],
      rewrite [if_neg l₄, sub_sub, add_sub_of_le g₃],
    end)

theorem unpair_mkpair (a b : nat) : unpair (mkpair a b) = (a, b) :=
by_cases
 (λ h : a < b,
  assert aux₁ : a ≤ b + b, from calc
    a   ≤ b   : le_of_lt h
    ... ≤ b+b : !le_add_right,
  begin
    esimp [mkpair],
    rewrite [if_pos h],
    esimp [unpair],
    rewrite [sqrt_offset_eq aux₁, add_sub_cancel_left, if_pos h]
  end)
 (λ h : ¬ a < b,
  have h₁ : b ≤ a, from le_of_not_gt h,
  assert aux₁ : a + b ≤ a + a, from add_le_add_left h₁ a,
  have   aux₂ : a + b ≥ a,     from !le_add_right,
  assert aux₃ : ¬ a + b < a,   from not_lt_of_ge aux₂,
  begin
    esimp [mkpair],
    rewrite [if_neg h],
    esimp [unpair],
    rewrite [add.assoc (a * a) a b, sqrt_offset_eq aux₁, *add_sub_cancel_left, if_neg aux₃]
  end)
end nat
