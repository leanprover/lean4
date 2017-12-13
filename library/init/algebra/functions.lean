/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.algebra.ordered_field

universe u

definition min {α : Type u} [decidable_linear_order α] (a b : α) : α := if a ≤ b then a else b
definition max {α : Type u} [decidable_linear_order α] (a b : α) : α := if a ≤ b then b else a
definition abs {α : Type u} [decidable_linear_ordered_comm_group α] (a : α) : α := max a (-a)

section
open decidable tactic
variables {α : Type u} [decidable_linear_order α]

private meta def min_tac_step : tactic unit :=
solve1 $ intros
>> `[unfold min max]
>> try `[simp [*, if_pos, if_neg]]
>> try `[apply le_refl]
>> try `[apply le_of_not_le, assumption]

meta def tactic.interactive.min_tac (a b : interactive.parse lean.parser.pexpr) : tactic unit :=
interactive.by_cases (none, ``(%%a ≤ %%b)); min_tac_step

lemma min_le_left (a b : α) : min a b ≤ a :=
by min_tac a b

lemma min_le_right (a b : α) : min a b ≤ b :=
by min_tac a b

lemma le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b :=
by min_tac a b

lemma le_max_left (a b : α) : a ≤ max a b :=
by min_tac a b

lemma le_max_right (a b : α) : b ≤ max a b :=
by min_tac a b

lemma max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c :=
by min_tac a b

lemma eq_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀{d}, d ≤ a → d ≤ b → d ≤ c) :  c = min a b :=
le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

lemma min_comm (a b : α) : min a b = min b a :=
eq_min (min_le_right a b) (min_le_left a b) (λ c h₁ h₂, le_min h₂ h₁)

lemma min_assoc (a b c : α) : min (min a b) c = min a (min b c) :=
begin
  apply eq_min,
  { apply le_trans, apply min_le_left, apply min_le_left },
  { apply le_min, apply le_trans, apply min_le_left, apply min_le_right, apply min_le_right },
  { intros d h₁ h₂, apply le_min, apply le_min h₁, apply le_trans h₂, apply min_le_left,
    apply le_trans h₂, apply min_le_right }
end

lemma min_left_comm : ∀ (a b c : α), min a (min b c) = min b (min a c) :=
left_comm (@min α _) (@min_comm α _) (@min_assoc α _)

@[simp]
lemma min_self (a : α) : min a a = a :=
by min_tac a a

@[ematch]
lemma min_eq_left {a b : α} (h : a ≤ b) : min a b = a :=
begin apply eq.symm, apply eq_min (le_refl _) h, intros, assumption end

@[ematch]
lemma min_eq_right {a b : α} (h : b ≤ a) : min a b = b :=
eq.subst (min_comm b a) (min_eq_left h)

lemma eq_max {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀{d}, a ≤ d → b ≤ d → c ≤ d) : c = max a b :=
le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)

lemma max_comm (a b : α) : max a b = max b a :=
eq_max (le_max_right a b) (le_max_left a b) (λ c h₁ h₂, max_le h₂ h₁)

lemma max_assoc (a b c : α) : max (max a b) c = max a (max b c) :=
begin
  apply eq_max,
  { apply le_trans, apply le_max_left a b, apply le_max_left },
  { apply max_le, apply le_trans, apply le_max_right a b, apply le_max_left, apply le_max_right },
  { intros d h₁ h₂, apply max_le, apply max_le h₁, apply le_trans (le_max_left _ _) h₂,
    apply le_trans (le_max_right _ _) h₂}
end

lemma max_left_comm : ∀ (a b c : α), max a (max b c) = max b (max a c) :=
left_comm (@max α _) (@max_comm α _) (@max_assoc α _)

@[simp]
lemma max_self (a : α) : max a a = a :=
by min_tac a a

lemma max_eq_left {a b : α} (h : b ≤ a) : max a b = a :=
begin apply eq.symm, apply eq_max (le_refl _) h, intros, assumption end

lemma max_eq_right {a b : α} (h : a ≤ b) : max a b = b :=
eq.subst (max_comm b a) (max_eq_left h)

/- these rely on lt_of_lt -/

lemma min_eq_left_of_lt {a b : α} (h : a < b) : min a b = a :=
min_eq_left (le_of_lt h)

lemma min_eq_right_of_lt {a b : α} (h : b < a) : min a b = b :=
min_eq_right (le_of_lt h)

lemma max_eq_left_of_lt {a b : α} (h : b < a) : max a b = a :=
max_eq_left (le_of_lt h)

lemma max_eq_right_of_lt {a b : α} (h : a < b) : max a b = b :=
max_eq_right (le_of_lt h)

/- these use the fact that it is a linear ordering -/

lemma lt_min {a b c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c :=
or.elim (le_or_gt b c)
  (assume h : b ≤ c, by min_tac b c)
  (assume h : b > c, by min_tac b c)

lemma max_lt {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
or.elim (le_or_gt a b)
  (assume h : a ≤ b, by min_tac a b)
  (assume h : a > b, by min_tac a b)
end


section
variables {α : Type u} [decidable_linear_ordered_cancel_comm_monoid α]

lemma min_add_add_left (a b c : α) : min (a + b) (a + c) = a + min b c :=
eq.symm (eq_min
  (show a + min b c ≤ a + b, from add_le_add_left (min_le_left _ _)  _)
  (show a + min b c ≤ a + c, from add_le_add_left (min_le_right _ _)  _)
  (assume d,
    assume : d ≤ a + b,
    assume : d ≤ a + c,
    decidable.by_cases
      (assume : b ≤ c, by rwa [min_eq_left this])
      (assume : ¬ b ≤ c, by rwa [min_eq_right (le_of_lt (lt_of_not_ge this))])))

lemma min_add_add_right (a b c : α) : min (a + c) (b + c) = min a b + c :=
begin rw [add_comm a c, add_comm b c, add_comm _ c], apply min_add_add_left end

lemma max_add_add_left (a b c : α) : max (a + b) (a + c) = a + max b c :=
eq.symm (eq_max
  (add_le_add_left (le_max_left _ _)  _)
  (add_le_add_left (le_max_right _ _) _)
  (assume d,
    assume : a + b ≤ d,
    assume : a + c ≤ d,
    decidable.by_cases
      (assume : b ≤ c, by rwa [max_eq_right this])
      (assume : ¬ b ≤ c, by rwa [max_eq_left (le_of_lt (lt_of_not_ge this))])))

lemma max_add_add_right (a b c : α) : max (a + c) (b + c) = max a b + c :=
begin rw [add_comm a c, add_comm b c, add_comm _ c], apply max_add_add_left end
end

section
variables {α : Type u} [decidable_linear_ordered_comm_group α]

lemma max_neg_neg (a b : α) : max (-a) (-b) = - min a b  :=
eq.symm (eq_max
  (show -a ≤ -(min a b), from neg_le_neg $ min_le_left a b)
  (show -b ≤ -(min a b), from neg_le_neg $ min_le_right a b)
  (assume d,
    assume H₁ : -a ≤ d,
    assume H₂ : -b ≤ d,
    have H : -d ≤ min a b,
      from le_min (neg_le_of_neg_le  H₁) (neg_le_of_neg_le H₂),
    show -(min a b) ≤ d, from neg_le_of_neg_le H))

lemma min_eq_neg_max_neg_neg (a b : α) : min a b = - max (-a) (-b) :=
by rw [max_neg_neg, neg_neg]

lemma min_neg_neg (a b : α) : min (-a) (-b) = - max a b :=
by rw [min_eq_neg_max_neg_neg, neg_neg, neg_neg]

lemma max_eq_neg_min_neg_neg (a b : α) : max a b = - min (-a) (-b) :=
by rw [min_neg_neg, neg_neg]
end

section decidable_linear_ordered_comm_group
variables {α : Type u} [decidable_linear_ordered_comm_group α]

lemma abs_of_nonneg {a : α} (h : a ≥ 0) : abs a = a :=
have h' : -a ≤ a, from le_trans (neg_nonpos_of_nonneg h) h,
max_eq_left h'

lemma abs_of_pos {a : α} (h : a > 0) : abs a = a :=
abs_of_nonneg (le_of_lt h)

lemma abs_of_nonpos {a : α} (h : a ≤ 0) : abs a = -a :=
have h' : a ≤ -a, from le_trans h (neg_nonneg_of_nonpos h),
max_eq_right h'

lemma abs_of_neg {a : α} (h : a < 0) : abs a = -a :=
abs_of_nonpos (le_of_lt h)

lemma abs_zero : abs 0 = (0:α) :=
abs_of_nonneg (le_refl _)

lemma abs_neg (a : α) : abs (-a) = abs a :=
begin unfold abs, rw [max_comm, neg_neg] end

lemma abs_pos_of_pos {a : α} (h : a > 0) : abs a > 0 :=
by rwa (abs_of_pos h)

lemma abs_pos_of_neg {a : α} (h : a < 0) : abs a > 0 :=
abs_neg a ▸ abs_pos_of_pos (neg_pos_of_neg h)

lemma abs_sub (a b : α) : abs (a - b) = abs (b - a) :=
by rw [← neg_sub, abs_neg]

lemma ne_zero_of_abs_ne_zero {a : α} (h : abs a ≠ 0) : a ≠ 0 :=
assume ha, h (eq.symm ha ▸ abs_zero)

/- these assume a linear order -/

lemma eq_zero_of_neg_eq {a : α} (h : -a = a) : a = 0 :=
match lt_trichotomy a 0 with
| or.inl h₁ :=
  have a > 0, from h ▸ neg_pos_of_neg h₁,
  absurd h₁ (lt_asymm this)
| or.inr (or.inl h₁) := h₁
| or.inr (or.inr h₁) :=
  have a < 0, from h ▸ neg_neg_of_pos h₁,
  absurd h₁ (lt_asymm this)
end

lemma abs_nonneg (a : α) : abs a ≥ 0 :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a, by rwa (abs_of_nonneg h))
  (assume h : a ≤ 0, calc
       0 ≤ -a    : neg_nonneg_of_nonpos h
     ... = abs a : eq.symm (abs_of_nonpos h))

lemma abs_abs (a : α) : abs (abs a) = abs a :=
abs_of_nonneg $ abs_nonneg a

lemma le_abs_self (a : α) : a ≤ abs a :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a,
   begin rw [abs_of_nonneg h] end)
  (assume h : a ≤ 0, le_trans h $ abs_nonneg a)

lemma neg_le_abs_self (a : α) : -a ≤ abs a :=
abs_neg a ▸ le_abs_self (-a)

lemma eq_zero_of_abs_eq_zero {a : α} (h : abs a = 0) : a = 0 :=
have h₁ : a ≤ 0, from h ▸ le_abs_self a,
have h₂ : -a ≤ 0, from h ▸ abs_neg a ▸ le_abs_self (-a),
le_antisymm h₁ (nonneg_of_neg_nonpos h₂)

lemma eq_of_abs_sub_eq_zero {a b : α} (h : abs (a - b) = 0) : a = b :=
have a - b = 0, from eq_zero_of_abs_eq_zero h,
show a = b, from eq_of_sub_eq_zero this

lemma abs_pos_of_ne_zero {a : α} (h : a ≠ 0) : abs a > 0 :=
or.elim (lt_or_gt_of_ne h) abs_pos_of_neg abs_pos_of_pos

lemma abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (abs a) :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a, eq.symm (abs_of_nonneg h) ▸ h1)
  (assume h : a ≤ 0, eq.symm (abs_of_nonpos h) ▸ h2)

lemma abs_le_of_le_of_neg_le {a b : α} (h1 : a ≤ b) (h2 : -a ≤ b) : abs a ≤ b :=
abs_by_cases (λ x : α, x ≤ b) h1 h2

lemma abs_lt_of_lt_of_neg_lt {a b : α} (h1 : a < b) (h2 : -a < b) : abs a < b :=
abs_by_cases (λ x : α, x < b) h1 h2

private lemma aux1 {a b : α} (h1 : a + b ≥ 0) (h2 : a ≥ 0) : abs (a + b) ≤ abs a + abs b :=
decidable.by_cases
  (assume h3 : b ≥ 0, calc
    abs (a + b) ≤ abs (a + b)   : by apply le_refl
            ... = a + b         : by rw (abs_of_nonneg h1)
            ... = abs a + b     : by rw (abs_of_nonneg h2)
            ... = abs a + abs b : by rw (abs_of_nonneg h3))
 (assume h3 : ¬ b ≥ 0,
  have h4 : b ≤ 0, from le_of_lt (lt_of_not_ge h3),
  calc
    abs (a + b) = a + b         : by rw (abs_of_nonneg h1)
            ... = abs a + b     : by rw (abs_of_nonneg h2)
            ... ≤ abs a + 0     : add_le_add_left h4 _
            ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos h4) _
            ... = abs a + abs b : by rw (abs_of_nonpos h4))

private lemma aux2 {a b : α} (h1 : a + b ≥ 0) : abs (a + b) ≤ abs a + abs b :=
or.elim (le_total b 0)
 (assume h2 : b ≤ 0,
  have h3 : ¬ a < 0, from
    assume h4 : a < 0,
    have h5 : a + b < 0,
      begin
        have aux := add_lt_add_of_lt_of_le h4 h2,
        rwa [add_zero] at aux
      end,
    not_lt_of_ge h1 h5,
  aux1 h1 (le_of_not_gt h3))
 (assume h2 : 0 ≤ b,
  begin
    have h3 : abs (b + a) ≤ abs b + abs a,
    begin
      rw add_comm at h1,
      exact aux1 h1 h2
    end,
    rw [add_comm, add_comm (abs a)],
    exact h3
  end)

lemma abs_add_le_abs_add_abs (a b : α) : abs (a + b) ≤ abs a + abs b :=
or.elim (le_total 0 (a + b))
  (assume h2 : 0 ≤ a + b, aux2 h2)
  (assume h2 : a + b ≤ 0,
   have h3 : -a + -b = -(a + b), by rw neg_add,
   have h4 : -(a + b) ≥ 0, from neg_nonneg_of_nonpos h2,
   have h5   : -a + -b ≥ 0, begin rw [← h3] at h4, exact h4 end,
   calc
      abs (a + b) = abs (-a + -b)   : by rw [← abs_neg, neg_add]
              ... ≤ abs (-a) + abs (-b) : aux2 h5
              ... = abs a + abs b       : by rw [abs_neg, abs_neg])

lemma abs_sub_abs_le_abs_sub (a b : α) : abs a - abs b ≤ abs (a - b) :=
have h1 : abs a - abs b + abs b ≤ abs (a - b) + abs b, from
calc
   abs a - abs b + abs b = abs a                 : by rw sub_add_cancel
                     ... = abs (a - b + b)       : by rw sub_add_cancel
                     ... ≤ abs (a - b) + abs b   : by apply abs_add_le_abs_add_abs,
le_of_add_le_add_right h1

lemma abs_sub_le (a b c : α) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
calc
    abs (a - c) = abs (a - b + (b - c))     : by rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
                                                    add_assoc, neg_add_cancel_left]
            ... ≤ abs (a - b) + abs (b - c) : by apply abs_add_le_abs_add_abs

lemma abs_add_three (a b c : α) : abs (a + b + c) ≤ abs a + abs b + abs c :=
begin
  apply le_trans,
  apply abs_add_le_abs_add_abs,
  apply le_trans,
  apply add_le_add_right,
  apply abs_add_le_abs_add_abs,
  apply le_refl
end

lemma dist_bdd_within_interval {a b lb ub : α} (h : lb < ub) (hal : lb ≤ a) (hau : a ≤ ub)
      (hbl : lb ≤ b) (hbu : b ≤ ub) : abs (a - b) ≤ ub - lb :=
begin
  cases (decidable.em (b ≤ a)) with hba hba,
  rw (abs_of_nonneg (sub_nonneg_of_le hba)),
  apply sub_le_sub,
  apply hau,
  apply hbl,
  rw [abs_of_neg (sub_neg_of_lt (lt_of_not_ge hba)), neg_sub],
  apply sub_le_sub,
  apply hbu,
  apply hal
end

end decidable_linear_ordered_comm_group


section decidable_linear_ordered_comm_ring
variables {α : Type u} [decidable_linear_ordered_comm_ring α]

lemma abs_mul (a b : α) : abs (a * b) = abs a * abs b :=
or.elim (le_total 0 a)
 (assume h1 : 0 ≤ a,
   or.elim (le_total 0 b)
      (assume h2 : 0 ≤ b,
        calc
          abs (a * b) = a * b         : abs_of_nonneg (mul_nonneg h1 h2)
                  ... = abs a * b     : by rw (abs_of_nonneg h1)
                  ... = abs a * abs b : by rw (abs_of_nonneg h2))
      (assume h2 : b ≤ 0,
        calc
          abs (a * b) = -(a * b)      : abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h1 h2)
                  ... = a * -b        : by rw neg_mul_eq_mul_neg
                  ... = abs a * -b    : by rw (abs_of_nonneg h1)
                  ... = abs a * abs b : by rw (abs_of_nonpos h2)))
  (assume h1 : a ≤ 0,
    or.elim (le_total 0 b)
      (assume h2 : 0 ≤ b,
        calc
          abs (a * b) = -(a * b)      : abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg h1 h2)
                  ... = -a * b        : by rw neg_mul_eq_neg_mul
                  ... = abs a * b     : by rw (abs_of_nonpos h1)
                  ... = abs a * abs b : by rw (abs_of_nonneg h2))
      (assume h2 : b ≤ 0,
        calc
          abs (a * b) = a * b         : abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos h1 h2)
                  ... = -a * -b       : by rw neg_mul_neg
                  ... = abs a * -b    : by rw (abs_of_nonpos h1)
                  ... = abs a * abs b : by rw (abs_of_nonpos h2)))


lemma abs_mul_abs_self (a : α) : abs a * abs a = a * a :=
abs_by_cases (λ x, x * x = a * a) rfl (neg_mul_neg a a)

lemma abs_mul_self (a : α) : abs (a * a) = a * a :=
by rw [abs_mul, abs_mul_abs_self]

lemma sub_le_of_abs_sub_le_left {a b c : α} (h : abs (a - b) ≤ c) : b - c ≤ a :=
if hz : 0 ≤ a - b then
  (calc
      a ≥ b     : le_of_sub_nonneg hz
    ... ≥ b - c : sub_le_self _ (le_trans (abs_nonneg _) h))
else
  have habs : b - a ≤ c, by rwa [abs_of_neg (lt_of_not_ge hz), neg_sub] at h,
  have habs' : b ≤ c + a, from le_add_of_sub_right_le habs,
  sub_left_le_of_le_add habs'

lemma sub_le_of_abs_sub_le_right {a b c : α} (h : abs (a - b) ≤ c) : a - c ≤ b :=
sub_le_of_abs_sub_le_left (abs_sub a b ▸ h)

lemma sub_lt_of_abs_sub_lt_left {a b c : α} (h : abs (a - b) < c) : b - c < a :=
if hz : 0 ≤ a - b then
   (calc
      a ≥ b     : le_of_sub_nonneg hz
    ... > b - c : sub_lt_self _ (lt_of_le_of_lt (abs_nonneg _) h))
else
  have habs : b - a < c, by rwa [abs_of_neg (lt_of_not_ge hz), neg_sub] at h,
  have habs' : b < c + a, from lt_add_of_sub_right_lt habs,
  sub_left_lt_of_lt_add habs'


lemma sub_lt_of_abs_sub_lt_right {a b c : α} (h : abs (a - b) < c) : a - c < b :=
sub_lt_of_abs_sub_lt_left (abs_sub a b ▸ h)

lemma abs_sub_square (a b : α) : abs (a - b) * abs (a - b) = a * a + b * b - (1 + 1) * a * b :=
begin
  rw abs_mul_abs_self,
  simp [left_distrib, right_distrib, add_assoc, add_comm, add_left_comm, mul_comm]
end

lemma eq_zero_of_mul_self_add_mul_self_eq_zero {x y : α} (h : x * x + y * y = 0) : x = 0 :=
have x * x ≤ (0 : α), from calc
  x * x ≤ x * x + y * y : le_add_of_nonneg_right (mul_self_nonneg y)
    ... = 0             : h,
eq_zero_of_mul_self_eq_zero (le_antisymm this (mul_self_nonneg x))

lemma abs_abs_sub_abs_le_abs_sub (a b : α) : abs (abs a - abs b) ≤ abs (a - b) :=
begin
   apply nonneg_le_nonneg_of_squares_le,
   apply abs_nonneg,
   iterate {rw abs_sub_square},
   iterate {rw abs_mul_abs_self},
   apply sub_le_sub_left,
   iterate {rw mul_assoc},
   apply mul_le_mul_of_nonneg_left,
   rw [← abs_mul],
   apply le_abs_self,
   apply le_of_lt,
   apply add_pos,
   apply zero_lt_one,
   apply zero_lt_one
end

end decidable_linear_ordered_comm_ring

section discrete_linear_ordered_field
variables {α : Type u} [discrete_linear_ordered_field α]

lemma abs_div (a b : α) : abs (a / b) = abs a / abs b :=
decidable.by_cases
  (assume h : b = 0, by rw [h, abs_zero, div_zero, div_zero, abs_zero])
  (assume h : b ≠ 0,
   have h₁ : abs b ≠ 0, from
     assume h₂, h (eq_zero_of_abs_eq_zero h₂),
   eq_div_of_mul_eq _ _ h₁
   (show abs (a / b) * abs b = abs a, by rw [← abs_mul, div_mul_cancel _ h]))

lemma abs_one_div (a : α) : abs (1 / a) = 1 / abs a :=
by rw [abs_div, abs_of_nonneg (zero_le_one : 1 ≥ (0 : α))]

end discrete_linear_ordered_field
