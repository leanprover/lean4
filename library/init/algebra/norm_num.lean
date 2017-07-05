/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis and Leonardo de Moura
-/
prelude
import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas

namespace norm_num
universe u
variable {α : Type u}

def add1 [has_add α] [has_one α] (a : α) : α :=
a + 1

local attribute [reducible] bit0 bit1 add1
local attribute [simp] right_distrib left_distrib

private meta def u : tactic unit :=
`[unfold bit0 bit1 add1]

private meta def usimp : tactic unit :=
u >> `[simp]

lemma mul_zero [mul_zero_class α] (a : α) : a * 0 = 0 :=
by simp

lemma zero_mul [mul_zero_class α] (a : α) : 0 * a = 0 :=
by simp

lemma mul_one [monoid α] (a : α) : a * 1 = a :=
by simp

lemma mul_bit0 [distrib α] (a b : α) : a * (bit0 b) = bit0 (a * b) :=
by simp

lemma mul_bit0_helper [distrib α] (a b t : α) (h : a * b = t) : a * (bit0 b) = bit0 t :=
begin rw [← h], simp end

lemma mul_bit1 [semiring α] (a b : α) : a * (bit1 b) = bit0 (a * b) + a :=
by simp

lemma mul_bit1_helper [semiring α] (a b s t : α) (hs : a * b = s) (ht : bit0 s + a  = t) :
        a * (bit1 b) = t :=
by simp [hs, ht]

lemma subst_into_prod [has_mul α] (l r tl tr t : α) (prl : l = tl) (prr : r = tr) (prt : tl * tr = t) : l * r = t :=
by simp [prl, prr, prt]

lemma mk_cong (op : α → α) (a b : α) (h : a = b) : op a = op b :=
by simp [h]

lemma neg_add_neg_eq_of_add_add_eq_zero [add_comm_group α] (a b c : α) (h : c + a + b = 0) : -a + -b = c :=
begin
  apply add_neg_eq_of_eq_add,
  apply neg_eq_of_add_eq_zero,
  simp at h, simp, assumption
end

lemma neg_add_neg_helper [add_comm_group α] (a b c : α) (h : a + b = c) : -a + -b = -c :=
begin apply @neg_inj α, simp [neg_add, neg_neg], assumption end

lemma neg_add_pos_eq_of_eq_add [add_comm_group α] (a b c : α) (h : b = c + a) : -a + b = c :=
begin apply neg_add_eq_of_eq_add, simp at h, assumption end

lemma neg_add_pos_helper1 [add_comm_group α] (a b c : α) (h : b + c = a) : -a + b = -c :=
begin apply neg_add_eq_of_eq_add, apply eq_add_neg_of_add_eq h end

lemma neg_add_pos_helper2 [add_comm_group α] (a b c : α) (h : a + c = b) : -a + b = c :=
begin apply neg_add_eq_of_eq_add, rw h end

lemma pos_add_neg_helper [add_comm_group α] (a b c : α) (h : b + a = c) : a + b = c :=
by rw [← h, add_comm a b]

lemma subst_into_subtr [add_group α] (l r t : α) (h : l + -r = t) : l - r = t :=
by simp [h]

lemma neg_neg_helper [add_group α] (a b : α) (h : a = -b) : -a = b :=
by simp [h]

lemma neg_mul_neg_helper [ring α] (a b c : α) (h : a * b = c) : (-a) * (-b) = c :=
by simp [h]

lemma neg_mul_pos_helper [ring α] (a b c : α) (h : a * b = c) : (-a) * b = -c :=
by simp [h]

lemma pos_mul_neg_helper [ring α] (a b c : α) (h : a * b = c) : a * (-b) = -c :=
by simp [h]

lemma div_add_helper [field α] (n d b c val : α) (hd : d ≠ 0) (h : n + b * d = val)
        (h2 : c * d = val) : n / d + b = c :=
begin
  apply eq_of_mul_eq_mul_of_nonzero_right hd,
  rw [h2, ← h, right_distrib, div_mul_cancel _ hd]
end

lemma add_div_helper [field α] (n d b c val : α) (hd : d ≠ 0) (h : d * b + n = val)
        (h2 : d * c = val) : b + n / d = c :=
begin
  apply eq_of_mul_eq_mul_of_nonzero_left hd,
  rw [h2, ← h, left_distrib, mul_div_cancel' _ hd]
end

lemma div_mul_helper [field α] (n d c v : α) (hd : d ≠ 0) (h : (n * c) / d = v) :
        (n / d) * c = v :=
by rw [← h, field.div_mul_eq_mul_div_comm _ _ hd, mul_div_assoc]

lemma mul_div_helper [field α] (a n d v : α) (hd : d ≠ 0) (h : (a * n) / d = v) :
        a * (n / d) = v :=
by rw [← h, mul_div_assoc]

lemma nonzero_of_div_helper [field α] (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 :=
begin
  intro hab,
  have habb : (a / b) * b = 0, rw [hab, zero_mul],
  rw [div_mul_cancel _ hb] at habb,
  exact ha habb
end

lemma div_helper [field α] (n d v : α) (hd : d ≠ 0) (h : v * d = n) : n / d = v :=
begin
  apply eq_of_mul_eq_mul_of_nonzero_right hd,
  rw (div_mul_cancel _ hd),
  exact eq.symm h
end

lemma div_eq_div_helper [field α] (a b c d v : α) (h1 : a * d = v) (h2 : c * b = v)
        (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d :=
begin
  apply eq_div_of_mul_eq,
  exact hd,
  rw div_mul_eq_mul_div,
  apply eq.symm,
  apply eq_div_of_mul_eq,
  exact hb,
  rw [h1, h2]
end

lemma subst_into_div [has_div α] (a₁ b₁ a₂ b₂ v : α) (h : a₁ / b₁ = v) (h1 : a₂ = a₁)
      (h2 : b₂ = b₁) : a₂ / b₂ = v :=
by rw [h1, h2, h]


lemma add_comm_four [add_comm_semigroup α] (a b : α) : a + a + (b + b) = (a + b) + (a + b) :=
by simp

lemma add_comm_middle [add_comm_semigroup α] (a b c : α) : a + b + c = a + c + b :=
by simp

lemma bit0_add_bit0 [add_comm_semigroup α] (a b : α) : bit0 a + bit0 b = bit0 (a + b) :=
by usimp

lemma bit0_add_bit0_helper [add_comm_semigroup α] (a b t : α) (h : a + b = t) :
        bit0 a + bit0 b = bit0 t :=
begin rw [← h], usimp end

lemma bit1_add_bit0 [add_comm_semigroup α] [has_one α] (a b : α) : bit1 a + bit0 b = bit1 (a + b) :=
by usimp

lemma bit1_add_bit0_helper [add_comm_semigroup α] [has_one α] (a b t : α)
        (h : a + b = t) : bit1 a + bit0 b = bit1 t :=
begin rw [← h], usimp end

lemma bit0_add_bit1 [add_comm_semigroup α] [has_one α] (a b : α) :
        bit0 a + bit1 b = bit1 (a + b) :=
by usimp

lemma bit0_add_bit1_helper [add_comm_semigroup α] [has_one α] (a b t : α)
        (h : a + b = t) : bit0 a + bit1 b = bit1 t :=
begin rw [← h], usimp end

lemma bit1_add_bit1 [add_comm_semigroup α] [has_one α] (a b : α) :
        bit1 a + bit1 b = bit0 (add1 (a + b)) :=
by usimp

lemma bit1_add_bit1_helper [add_comm_semigroup α] [has_one α] (a b t s : α)
        (h : (a + b) = t) (h2 : add1 t = s) : bit1 a + bit1 b = bit0 s :=
begin rw [← h] at h2, rw [← h2], usimp end

lemma bin_add_zero [add_monoid α] (a : α) : a + 0 = a :=
by simp

lemma bin_zero_add [add_monoid α] (a : α) : 0 + a = a :=
by simp

lemma one_add_bit0 [add_comm_semigroup α] [has_one α] (a : α) : 1 + bit0 a = bit1 a :=
begin unfold bit0 bit1, simp end

lemma bit0_add_one [has_add α] [has_one α] (a : α) : bit0 a + 1 = bit1 a :=
rfl

lemma bit1_add_one [has_add α] [has_one α] (a : α) : bit1 a + 1 = add1 (bit1 a) :=
rfl

lemma bit1_add_one_helper [has_add α] [has_one α] (a t : α) (h : add1 (bit1 a) = t) :
        bit1 a + 1 = t :=
by rw [← h]

lemma one_add_bit1 [add_comm_semigroup α] [has_one α] (a : α) : 1 + bit1 a = add1 (bit1 a) :=
begin unfold bit0 bit1 add1, simp end

lemma one_add_bit1_helper [add_comm_semigroup α] [has_one α] (a t : α)
        (h : add1 (bit1 a) = t) : 1 + bit1 a = t :=
begin rw [← h], usimp end

lemma add1_bit0 [has_add α] [has_one α] (a : α) : add1 (bit0 a) = bit1 a :=
rfl

lemma add1_bit1 [add_comm_semigroup α] [has_one α] (a : α) :
        add1 (bit1 a) = bit0 (add1 a) :=
by usimp

lemma add1_bit1_helper [add_comm_semigroup α] [has_one α] (a t : α) (h : add1 a = t) :
        add1 (bit1 a) = bit0 t :=
begin rw [← h], usimp end

lemma add1_one [has_add α] [has_one α] : add1 (1 : α) = bit0 1 :=
rfl

lemma add1_zero [add_monoid α] [has_one α] : add1 (0 : α) = 1 :=
by usimp

lemma one_add_one [has_add α] [has_one α] : (1 : α) + 1 = bit0 1 :=
rfl

lemma subst_into_sum [has_add α] (l r tl tr t : α) (prl : l = tl) (prr : r = tr)
        (prt : tl + tr = t) : l + r = t :=
by rw [← prt, prr, prl]

lemma neg_zero_helper [add_group α] (a : α) (h : a = 0) : - a = 0 :=
begin rw h, simp end

lemma pos_bit0_helper [linear_ordered_semiring α] (a : α) (h : a > 0) : bit0 a > 0 :=
begin u, apply add_pos h h end

lemma nonneg_bit0_helper [linear_ordered_semiring α] (a : α) (h : a ≥ 0) : bit0 a ≥ 0 :=
begin u, apply add_nonneg h h end

lemma pos_bit1_helper [linear_ordered_semiring α] (a : α) (h : a ≥ 0) : bit1 a > 0 :=
begin
  u,
  apply add_pos_of_nonneg_of_pos,
  apply nonneg_bit0_helper _ h,
  apply zero_lt_one
end

lemma nonneg_bit1_helper [linear_ordered_semiring α] (a : α) (h : a ≥ 0) : bit1 a ≥ 0 :=
begin apply le_of_lt,  apply pos_bit1_helper _ h end

lemma nonzero_of_pos_helper [linear_ordered_semiring α] (a : α) (h : a > 0) : a ≠ 0 :=
  ne_of_gt h

lemma nonzero_of_neg_helper [linear_ordered_ring α] (a : α) (h : a ≠ 0) : -a ≠ 0 :=
begin intro ha, apply h, apply neg_inj, rwa neg_zero end

lemma sub_nat_zero_helper {a b c d: ℕ} (hac : a = c) (hbd : b = d) (hcd : c < d) : a - b = 0 :=
begin
 simp *, apply nat.sub_eq_zero_of_le, apply le_of_lt, assumption
end

lemma sub_nat_pos_helper {a b c d e : ℕ} (hac : a = c) (hbd : b = d) (hced : e + d = c) :
  a - b = e :=
begin
simp *, rw [← hced, nat.add_sub_cancel]
end

end norm_num
