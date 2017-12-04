/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.algebra.order init.algebra.group

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

universe u

class ordered_cancel_comm_monoid (α : Type u)
      extends add_comm_monoid α, add_left_cancel_semigroup α,
              add_right_cancel_semigroup α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c)

section ordered_cancel_comm_monoid
variable {α : Type u}
variable [s : ordered_cancel_comm_monoid α]

lemma add_le_add_left {a b : α} (h : a ≤ b) (c : α) : c + a ≤ c + b :=
@ordered_cancel_comm_monoid.add_le_add_left α s a b h c

lemma le_of_add_le_add_left {a b c : α} (h : a + b ≤ a + c) : b ≤ c :=
@ordered_cancel_comm_monoid.le_of_add_le_add_left α s a b c h
end ordered_cancel_comm_monoid

section ordered_cancel_comm_monoid
variable {α : Type u}
variable [ordered_cancel_comm_monoid α]

lemma add_lt_add_left {a b : α} (h : a < b) (c : α) : c + a < c + b :=
lt_of_le_not_le (add_le_add_left (le_of_lt h) _) $
  mt le_of_add_le_add_left (not_le_of_gt h)

lemma lt_of_add_lt_add_left {a b c : α} (h : a + b < a + c) : b < c :=
lt_of_le_not_le (le_of_add_le_add_left (le_of_lt h)) $
  mt (λ h, add_le_add_left h _) (not_le_of_gt h)

lemma add_le_add_right {a b : α} (h : a ≤ b) (c : α) : a + c ≤ b + c :=
add_comm c a ▸ add_comm c b ▸ add_le_add_left h c

theorem add_lt_add_right {a b : α} (h : a < b) (c : α) : a + c < b + c :=
begin
 rw [add_comm a c, add_comm b c],
 exact (add_lt_add_left h c)
end

lemma add_le_add {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_add_right h₁ c) (add_le_add_left h₂ b)

lemma le_add_of_nonneg_right {a b : α} (h : b ≥ 0) : a ≤ a + b :=
have a + b ≥ a + 0, from add_le_add_left h a,
by rwa add_zero at this

lemma le_add_of_nonneg_left {a b : α} (h : b ≥ 0) : a ≤ b + a :=
have 0 + a ≤ b + a, from add_le_add_right h a,
by rwa zero_add at this

lemma add_lt_add {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
lt_trans (add_lt_add_right h₁ c) (add_lt_add_left h₂ b)

lemma add_lt_add_of_le_of_lt {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
lt_of_le_of_lt (add_le_add_right h₁ c) (add_lt_add_left h₂ b)

lemma add_lt_add_of_lt_of_le {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
lt_of_lt_of_le (add_lt_add_right h₁ c) (add_le_add_left h₂ b)

lemma lt_add_of_pos_right (a : α) {b : α} (h : b > 0) : a < a + b :=
have a + 0 < a + b, from add_lt_add_left h a,
by rwa [add_zero] at this

lemma lt_add_of_pos_left (a : α) {b : α} (h : b > 0) : a < b + a :=
have 0 + a < b + a, from add_lt_add_right h a,
by rwa [zero_add] at this

lemma le_of_add_le_add_right {a b c : α} (h : a + b ≤ c + b) : a ≤ c :=
le_of_add_le_add_left
  (show b + a ≤ b + c, begin rw [add_comm b a, add_comm b c], assumption end)

lemma lt_of_add_lt_add_right {a b c : α} (h : a + b < c + b) : a < c :=
lt_of_add_lt_add_left
  (show b + a < b + c, begin rw [add_comm b a, add_comm b c], assumption end)

-- here we start using properties of zero.
lemma add_nonneg {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
zero_add (0:α) ▸ (add_le_add ha hb)

lemma add_pos {a b : α} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  zero_add (0:α) ▸ (add_lt_add ha hb)

lemma add_pos_of_pos_of_nonneg {a b : α} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
zero_add (0:α) ▸ (add_lt_add_of_lt_of_le ha hb)

lemma add_pos_of_nonneg_of_pos {a b : α} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
zero_add (0:α) ▸ (add_lt_add_of_le_of_lt ha hb)

lemma add_nonpos {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
zero_add (0:α) ▸ (add_le_add ha hb)

lemma add_neg {a b : α} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
zero_add (0:α) ▸ (add_lt_add ha hb)

lemma add_neg_of_neg_of_nonpos {a b : α} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
zero_add (0:α) ▸ (add_lt_add_of_lt_of_le ha hb)

lemma add_neg_of_nonpos_of_neg {a b : α} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
zero_add (0:α) ▸ (add_lt_add_of_le_of_lt ha hb)

lemma add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
    {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
iff.intro
  (assume hab : a + b = 0,
   have ha' : a ≤ 0, from
   calc
       a     = a + 0 : by rw add_zero
         ... ≤ a + b : add_le_add_left hb _
         ... = 0     : hab,
   have haz : a = 0, from le_antisymm ha' ha,
   have hb' : b ≤ 0, from
   calc
      b     = 0 + b : by rw zero_add
        ... ≤ a + b : by exact add_le_add_right ha _
        ... = 0     : hab,
   have hbz : b = 0, from le_antisymm hb' hb,
   and.intro haz hbz)
  (assume ⟨ha', hb'⟩,
   by rw [ha', hb', add_zero])

lemma le_add_of_nonneg_of_le {a b c : α} (ha : 0 ≤ a) (hbc : b ≤ c) : b ≤ a + c :=
zero_add b ▸ add_le_add ha hbc

lemma le_add_of_le_of_nonneg {a b c : α} (hbc : b ≤ c) (ha : 0 ≤ a) : b ≤ c + a :=
add_zero b ▸ add_le_add hbc ha

lemma lt_add_of_pos_of_le {a b c : α} (ha : 0 < a) (hbc : b ≤ c) : b < a + c :=
zero_add b ▸ add_lt_add_of_lt_of_le ha hbc

lemma lt_add_of_le_of_pos {a b c : α} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
add_zero b ▸ add_lt_add_of_le_of_lt hbc ha

lemma add_le_of_nonpos_of_le {a b c : α} (ha : a ≤ 0) (hbc : b ≤ c) : a + b ≤ c :=
zero_add c ▸ add_le_add ha hbc

lemma add_le_of_le_of_nonpos {a b c : α} (hbc : b ≤ c) (ha : a ≤ 0) : b + a ≤ c :=
add_zero c ▸ add_le_add hbc ha

lemma add_lt_of_neg_of_le {a b c : α} (ha : a < 0) (hbc : b ≤ c) : a + b < c :=
zero_add c ▸ add_lt_add_of_lt_of_le ha hbc

lemma add_lt_of_le_of_neg {a b c : α} (hbc : b ≤ c) (ha : a < 0) : b + a < c :=
add_zero c ▸ add_lt_add_of_le_of_lt hbc ha

lemma lt_add_of_nonneg_of_lt {a b c : α} (ha : 0 ≤ a) (hbc : b < c) : b < a + c :=
zero_add b ▸ add_lt_add_of_le_of_lt ha hbc

lemma lt_add_of_lt_of_nonneg {a b c : α} (hbc : b < c) (ha : 0 ≤ a) : b < c + a :=
add_zero b ▸ add_lt_add_of_lt_of_le hbc ha

lemma lt_add_of_pos_of_lt {a b c : α} (ha : 0 < a) (hbc : b < c) : b < a + c :=
zero_add b ▸ add_lt_add ha hbc

lemma lt_add_of_lt_of_pos {a b c : α} (hbc : b < c) (ha : 0 < a) : b < c + a :=
add_zero b ▸ add_lt_add hbc ha

lemma add_lt_of_nonpos_of_lt {a b c : α} (ha : a ≤ 0) (hbc : b < c) : a + b < c :=
zero_add c ▸ add_lt_add_of_le_of_lt ha hbc

lemma add_lt_of_lt_of_nonpos {a b c : α} (hbc : b < c) (ha : a ≤ 0)  : b + a < c :=
add_zero c ▸ add_lt_add_of_lt_of_le hbc ha

lemma add_lt_of_neg_of_lt {a b c : α} (ha : a < 0) (hbc : b < c) : a + b < c :=
zero_add c ▸ add_lt_add ha hbc

lemma add_lt_of_lt_of_neg {a b c : α} (hbc : b < c) (ha : a < 0) : b + a < c :=
add_zero c ▸ add_lt_add hbc ha

end ordered_cancel_comm_monoid

class ordered_comm_group (α : Type u) extends add_comm_group α, partial_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(add_lt_add_left : ∀ a b : α, a < b → ∀ c : α, c + a < c + b)

section ordered_comm_group
variable {α : Type u}
variable [ordered_comm_group α]

lemma ordered_comm_group.le_of_add_le_add_left {a b c : α} (h : a + b ≤ a + c) : b ≤ c :=
have -a + (a + b) ≤ -a + (a + c), from ordered_comm_group.add_le_add_left _ _ h _,
begin simp [neg_add_cancel_left] at this, assumption end

lemma ordered_comm_group.lt_of_add_lt_add_left {a b c : α} (h : a + b < a + c) : b < c :=
have -a + (a + b) < -a + (a + c), from ordered_comm_group.add_lt_add_left _ _ h _,
begin simp [neg_add_cancel_left] at this, assumption end
end ordered_comm_group

instance ordered_comm_group.to_ordered_cancel_comm_monoid (α : Type u) [s : ordered_comm_group α] : ordered_cancel_comm_monoid α :=
{ add_left_cancel       := @add_left_cancel α _,
  add_right_cancel      := @add_right_cancel α _,
  le_of_add_le_add_left := @ordered_comm_group.le_of_add_le_add_left α _,
  ..s }

section ordered_comm_group
variables {α : Type u} [ordered_comm_group α]

lemma neg_le_neg {a b : α} (h : a ≤ b) : -b ≤ -a :=
have 0 ≤ -a + b,           from add_left_neg a ▸ add_le_add_left h (-a),
have 0 + -b ≤ -a + b + -b, from add_le_add_right this (-b),
by rwa [add_neg_cancel_right, zero_add] at this

lemma le_of_neg_le_neg {a b : α} (h : -b ≤ -a) : a ≤ b :=
suffices -(-a) ≤ -(-b), from
  begin simp [neg_neg] at this, assumption end,
neg_le_neg h

lemma nonneg_of_neg_nonpos {a : α} (h : -a ≤ 0) : 0 ≤ a :=
have -a ≤ -0, by rwa neg_zero,
le_of_neg_le_neg this

lemma neg_nonpos_of_nonneg {a : α} (h : 0 ≤ a) : -a ≤ 0 :=
have -a ≤ -0, from neg_le_neg h,
by rwa neg_zero at this

lemma nonpos_of_neg_nonneg {a : α} (h : 0 ≤ -a) : a ≤ 0 :=
have -0 ≤ -a, by rwa neg_zero,
le_of_neg_le_neg this

lemma neg_nonneg_of_nonpos {a : α} (h : a ≤ 0) : 0 ≤ -a :=
have -0 ≤ -a, from neg_le_neg h,
by rwa neg_zero at this

lemma neg_lt_neg {a b : α} (h : a < b) : -b < -a :=
have 0 < -a + b, from add_left_neg a ▸ add_lt_add_left h (-a),
have 0 + -b < -a + b + -b, from add_lt_add_right this (-b),
by rwa [add_neg_cancel_right, zero_add] at this

lemma lt_of_neg_lt_neg {a b : α} (h : -b < -a) : a < b :=
neg_neg a ▸ neg_neg b ▸ neg_lt_neg h

lemma pos_of_neg_neg {a : α} (h : -a < 0) : 0 < a :=
have -a < -0, by rwa neg_zero,
lt_of_neg_lt_neg this

lemma neg_neg_of_pos {a : α} (h : 0 < a) : -a < 0 :=
have -a < -0, from neg_lt_neg h,
by rwa neg_zero at this

lemma neg_of_neg_pos {a : α} (h : 0 < -a) : a < 0 :=
have -0 < -a, by rwa neg_zero,
lt_of_neg_lt_neg this

lemma neg_pos_of_neg {a : α} (h : a < 0) : 0 < -a :=
have -0 < -a, from neg_lt_neg h,
by rwa neg_zero at this

lemma le_neg_of_le_neg {a b : α} (h : a ≤ -b) : b ≤ -a :=
begin
  have h := neg_le_neg h,
  rwa neg_neg at h
end

lemma neg_le_of_neg_le {a b : α} (h : -a ≤ b) : -b ≤ a :=
begin
  have h := neg_le_neg h,
  rwa neg_neg at h
end

lemma lt_neg_of_lt_neg {a b : α} (h : a < -b) : b < -a :=
begin
  have h := neg_lt_neg h,
  rwa neg_neg at h
end

lemma neg_lt_of_neg_lt {a b : α} (h : -a < b) : -b < a :=
begin
  have h := neg_lt_neg h,
  rwa neg_neg at h
end

lemma sub_nonneg_of_le {a b : α} (h : b ≤ a) : 0 ≤ a - b :=
begin
  have h := add_le_add_right h (-b),
  rwa add_right_neg at h
end

lemma le_of_sub_nonneg {a b : α} (h : 0 ≤ a - b) : b ≤ a :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_nonpos_of_le {a b : α} (h : a ≤ b) : a - b ≤ 0 :=
begin
  have h := add_le_add_right h (-b),
  rwa add_right_neg at h
end

lemma le_of_sub_nonpos {a b : α} (h : a - b ≤ 0) : a ≤ b :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_pos_of_lt {a b : α} (h : b < a) : 0 < a - b :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_right_neg at h
end

lemma lt_of_sub_pos {a b : α} (h : 0 < a - b) : b < a :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_neg_of_lt {a b : α} (h : a < b) : a - b < 0 :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_right_neg at h
end

lemma lt_of_sub_neg {a b : α} (h : a - b < 0) : a < b :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma add_le_of_le_neg_add {a b c : α} (h : b ≤ -a + c) : a + b ≤ c :=
begin
  have h := add_le_add_left h a,
  rwa add_neg_cancel_left at h
end

lemma le_neg_add_of_add_le {a b c : α} (h : a + b ≤ c) : b ≤ -a + c :=
begin
  have h := add_le_add_left h (-a),
  rwa neg_add_cancel_left at h
end

lemma add_le_of_le_sub_left {a b c : α} (h : b ≤ c - a) : a + b ≤ c :=
begin
  have h := add_le_add_left h a,
  rwa [← add_sub_assoc, add_comm a c, add_sub_cancel] at h
end

lemma le_sub_left_of_add_le {a b c : α} (h : a + b ≤ c) : b ≤ c - a :=
begin
  have h := add_le_add_right h (-a),
  rwa [add_comm a b, add_neg_cancel_right] at h
end

lemma add_le_of_le_sub_right {a b c : α} (h : a ≤ c - b) : a + b ≤ c :=
begin
  have h := add_le_add_right h b,
  rwa sub_add_cancel at h
end

lemma le_sub_right_of_add_le {a b c : α} (h : a + b ≤ c) : a ≤ c - b :=
begin
  have h := add_le_add_right h (-b),
  rwa add_neg_cancel_right at h
end

lemma le_add_of_neg_add_le {a b c : α} (h : -b + a ≤ c) : a ≤ b + c :=
begin
  have h := add_le_add_left h b,
  rwa add_neg_cancel_left at h
end

lemma neg_add_le_of_le_add {a b c : α} (h : a ≤ b + c) : -b + a ≤ c :=
begin
  have h := add_le_add_left h (-b),
  rwa neg_add_cancel_left at h
end

lemma le_add_of_sub_left_le {a b c : α} (h : a - b ≤ c) : a ≤ b + c :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, add_comm] at h
end

lemma sub_left_le_of_le_add {a b c : α} (h : a ≤ b + c) : a - b ≤ c :=
begin
  have h := add_le_add_right h (-b),
  rwa [add_comm b c, add_neg_cancel_right] at h
end

lemma le_add_of_sub_right_le {a b c : α} (h : a - c ≤ b) : a ≤ b + c :=
begin
  have h := add_le_add_right h c,
  rwa sub_add_cancel at h
end

lemma sub_right_le_of_le_add {a b c : α} (h : a ≤ b + c) : a - c ≤ b :=
begin
  have h := add_le_add_right h (-c),
  rwa add_neg_cancel_right at h
end

lemma le_add_of_neg_add_le_left {a b c : α} (h : -b + a ≤ c) : a ≤ b + c :=
begin
  rw add_comm at h,
  exact le_add_of_sub_left_le h
end

lemma neg_add_le_left_of_le_add {a b c : α} (h : a ≤ b + c) : -b + a ≤ c :=
begin
  rw add_comm,
  exact sub_left_le_of_le_add h
end

lemma le_add_of_neg_add_le_right {a b c : α} (h : -c + a ≤ b) : a ≤ b + c :=
begin
  rw add_comm at h,
  exact le_add_of_sub_right_le h
end

lemma neg_add_le_right_of_le_add {a b c : α} (h : a ≤ b + c) : -c + a ≤ b :=
begin
  rw add_comm at h,
  apply neg_add_le_left_of_le_add h
end

lemma le_add_of_neg_le_sub_left {a b c : α} (h : -a ≤ b - c) : c ≤ a + b :=
le_add_of_neg_add_le_left (add_le_of_le_sub_right h)

lemma neg_le_sub_left_of_le_add {a b c : α} (h : c ≤ a + b) : -a ≤ b - c :=
begin
  have h := le_neg_add_of_add_le (sub_left_le_of_le_add h),
  rwa add_comm at h
end

lemma le_add_of_neg_le_sub_right {a b c : α} (h : -b ≤ a - c) : c ≤ a + b :=
le_add_of_sub_right_le (add_le_of_le_sub_left h)

lemma neg_le_sub_right_of_le_add {a b c : α} (h : c ≤ a + b) : -b ≤ a - c :=
le_sub_left_of_add_le (sub_right_le_of_le_add h)

lemma sub_le_of_sub_le {a b c : α} (h : a - b ≤ c) : a - c ≤ b :=
sub_left_le_of_le_add (le_add_of_sub_right_le h)

lemma sub_le_sub_left {a b : α} (h : a ≤ b) (c : α) : c - b ≤ c - a :=
add_le_add_left (neg_le_neg h) c

lemma sub_le_sub_right {a b : α} (h : a ≤ b) (c : α) : a - c ≤ b - c :=
add_le_add_right h (-c)

lemma sub_le_sub {a b c d : α} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
add_le_add hab (neg_le_neg hcd)

lemma add_lt_of_lt_neg_add {a b c : α} (h : b < -a + c) : a + b < c :=
begin
  have h := add_lt_add_left h a,
  rwa add_neg_cancel_left at h
end

lemma lt_neg_add_of_add_lt {a b c : α} (h : a + b < c) : b < -a + c :=
begin
  have h := add_lt_add_left h (-a),
  rwa neg_add_cancel_left at h
end

lemma add_lt_of_lt_sub_left {a b c : α} (h : b < c - a) : a + b < c :=
begin
  have h := add_lt_add_left h a,
  rwa [← add_sub_assoc, add_comm a c, add_sub_cancel] at h
end

lemma lt_sub_left_of_add_lt {a b c : α} (h : a + b < c) : b < c - a :=
begin
  have h := add_lt_add_right h (-a),
  rwa [add_comm a b, add_neg_cancel_right] at h
end

lemma add_lt_of_lt_sub_right {a b c : α} (h : a < c - b) : a + b < c :=
begin
  have h := add_lt_add_right h b,
  rwa sub_add_cancel at h
end

lemma lt_sub_right_of_add_lt {a b c : α} (h : a + b < c) : a < c - b :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_neg_cancel_right at h
end

lemma lt_add_of_neg_add_lt {a b c : α} (h : -b + a < c) : a < b + c :=
begin
  have h := add_lt_add_left h b,
  rwa add_neg_cancel_left at h
end

lemma neg_add_lt_of_lt_add {a b c : α} (h : a < b + c) : -b + a < c :=
begin
  have h := add_lt_add_left h (-b),
  rwa neg_add_cancel_left at h
end

lemma lt_add_of_sub_left_lt {a b c : α} (h : a - b < c) : a < b + c :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, add_comm] at h
end

lemma sub_left_lt_of_lt_add {a b c : α} (h : a < b + c) : a - b < c :=
begin
  have h := add_lt_add_right h (-b),
  rwa [add_comm b c, add_neg_cancel_right] at h
end

lemma lt_add_of_sub_right_lt {a b c : α} (h : a - c < b) : a < b + c :=
begin
  have h := add_lt_add_right h c,
  rwa sub_add_cancel at h
end

lemma sub_right_lt_of_lt_add {a b c : α} (h : a < b + c) : a - c < b :=
begin
  have h := add_lt_add_right h (-c),
  rwa add_neg_cancel_right at h
end

lemma lt_add_of_neg_add_lt_left {a b c : α} (h : -b + a < c) : a < b + c :=
begin
  rw add_comm at h,
  exact lt_add_of_sub_left_lt h
end

lemma neg_add_lt_left_of_lt_add {a b c : α} (h : a < b + c) : -b + a < c :=
begin
  rw add_comm,
  exact sub_left_lt_of_lt_add h
end

lemma lt_add_of_neg_add_lt_right {a b c : α} (h : -c + a < b) : a < b + c :=
begin
  rw add_comm at h,
  exact lt_add_of_sub_right_lt h
end

lemma neg_add_lt_right_of_lt_add {a b c : α} (h : a < b + c) : -c + a < b :=
begin
  rw add_comm at h,
  apply neg_add_lt_left_of_lt_add h
end

lemma lt_add_of_neg_lt_sub_left {a b c : α} (h : -a < b - c) : c < a + b :=
lt_add_of_neg_add_lt_left (add_lt_of_lt_sub_right h)

lemma neg_lt_sub_left_of_lt_add {a b c : α} (h : c < a + b) : -a < b - c :=
begin
  have h := lt_neg_add_of_add_lt (sub_left_lt_of_lt_add h),
  rwa add_comm at h
end

lemma lt_add_of_neg_lt_sub_right {a b c : α} (h : -b < a - c) : c < a + b :=
lt_add_of_sub_right_lt (add_lt_of_lt_sub_left h)

lemma neg_lt_sub_right_of_lt_add {a b c : α} (h : c < a + b) : -b < a - c :=
lt_sub_left_of_add_lt (sub_right_lt_of_lt_add h)

lemma sub_lt_of_sub_lt {a b c : α} (h : a - b < c) : a - c < b :=
sub_left_lt_of_lt_add (lt_add_of_sub_right_lt h)

lemma sub_lt_sub_left {a b : α} (h : a < b) (c : α) : c - b < c - a :=
add_lt_add_left (neg_lt_neg h) c

lemma sub_lt_sub_right {a b : α} (h : a < b) (c : α) : a - c < b - c :=
add_lt_add_right h (-c)

lemma sub_lt_sub {a b c d : α} (hab : a < b) (hcd : c < d) : a - d < b - c :=
add_lt_add hab (neg_lt_neg hcd)

lemma sub_lt_sub_of_le_of_lt {a b c d : α} (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
add_lt_add_of_le_of_lt hab (neg_lt_neg hcd)

lemma sub_lt_sub_of_lt_of_le {a b c d : α} (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
add_lt_add_of_lt_of_le hab (neg_le_neg hcd)

lemma sub_le_self (a : α) {b : α} (h : b ≥ 0) : a - b ≤ a :=
calc
  a - b = a + -b : rfl
    ... ≤ a + 0  : add_le_add_left (neg_nonpos_of_nonneg h) _
    ... = a      : by rw add_zero

lemma sub_lt_self (a : α) {b : α} (h : b > 0) : a - b < a :=
calc
  a - b = a + -b : rfl
    ... < a + 0  : add_lt_add_left (neg_neg_of_pos h) _
    ... = a      : by rw add_zero

lemma add_le_add_three {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
      a + b + c ≤ d + e + f :=
begin
  apply le_trans,
  apply add_le_add,
  apply add_le_add,
  assumption',
  apply le_refl
end

end ordered_comm_group

class decidable_linear_ordered_comm_group (α : Type u)
    extends add_comm_group α, decidable_linear_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(add_lt_add_left : ∀ a b : α, a < b → ∀ c : α, c + a < c + b)

instance decidable_linear_ordered_comm_group.to_ordered_comm_group (α : Type u)
  [s : decidable_linear_ordered_comm_group α] : ordered_comm_group α :=
{ add := s.add, ..s }

class decidable_linear_ordered_cancel_comm_monoid (α : Type u)
      extends ordered_cancel_comm_monoid α, decidable_linear_order α
