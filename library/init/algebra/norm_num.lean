/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis and Leonardo de Moura
-/
prelude
import init.algebra.ring

namespace norm_num
universe variable u
variable {α : Type u}

def add1 [has_add α] [has_one α] (a : α) : α :=
a + 1

local attribute [reducible] bit0 bit1 add1
local attribute [simp] right_distrib left_distrib

lemma mul_zero [mul_zero_class α] (a : α) : a * 0 = 0 :=
by simp

lemma zero_mul [mul_zero_class α] (a : α) : 0 * a = 0 :=
by simp

lemma mul_one [monoid α] (a : α) : a * 1 = a :=
by simp

lemma mul_bit0 [distrib α] (a b : α) : a * (bit0 b) = bit0 (a * b) :=
by simp

lemma mul_bit0_helper [distrib α] (a b t : α) (h : a * b = t) : a * (bit0 b) = bit0 t :=
begin rw [-h], simp end

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
by rw [-h, add_comm a b]

lemma sub_eq_add_neg_helper [add_comm_group α] (t₁ t₂ e w₁ w₂: α) (h₁ : t₁ = w₁)
        (h₂ : t₂ = w₂) (h₃ : w₁ + -w₂ = e) : t₁ - t₂ = e :=
by rw [h₁, h₂, sub_eq_add_neg, h₃]

lemma pos_add_pos_helper [add_comm_group α] (a b c d₁ d₂ : α) (h₁ : a = d₁) (h₂ : b = d₂)
        (h₃ : d₁ + d₂ = c) : a + b = c :=
by rw [h₁, h₂, h₃]

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

end norm_num
