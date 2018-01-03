/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.bool.basic init.meta

attribute [simp] cond bor band bnot bxor

@[simp] lemma {u} cond_a_a {α : Type u} (b : bool) (a : α) : cond b a a = a :=
by cases b; simp

@[simp] lemma band_self (b : bool) : b && b = b :=
by cases b; simp

@[simp] lemma band_tt (b : bool) : b && tt = b :=
by cases b; simp

@[simp] lemma band_ff (b : bool) : b && ff = ff :=
by cases b; simp

@[simp] lemma tt_band (b : bool) : tt && b = b :=
by cases b; simp

@[simp] lemma ff_band (b : bool) : ff && b = ff :=
by cases b; simp

@[simp] lemma bor_self (b : bool) : b || b = b :=
by cases b; simp

@[simp] lemma bor_tt (b : bool) : b || tt = tt :=
by cases b; simp

@[simp] lemma bor_ff (b : bool) : b || ff = b :=
by cases b; simp

@[simp] lemma tt_bor (b : bool) : tt || b = tt :=
by cases b; simp

@[simp] lemma ff_bor (b : bool) : ff || b = b :=
by cases b; simp

@[simp] lemma bxor_self (b : bool) : bxor b b = ff :=
by cases b; simp

@[simp] lemma bxor_tt (b : bool) : bxor b tt = bnot b :=
by cases b; simp

@[simp] lemma bxor_ff (b : bool) : bxor b ff = b :=
by cases b; simp

@[simp] lemma tt_bxor (b : bool) : bxor tt b = bnot b :=
by cases b; simp

@[simp] lemma ff_bxor (b : bool) : bxor ff b = b :=
by cases b; simp

@[simp] lemma bnot_bnot (b : bool) : bnot (bnot b) = b :=
by cases b; simp

@[simp] lemma tt_eq_ff_eq_false : ¬(tt = ff) :=
by contradiction

@[simp] lemma ff_eq_tt_eq_false : ¬(ff = tt) :=
by contradiction

@[simp] lemma eq_ff_eq_not_eq_tt (b : bool) : (¬(b = tt)) = (b = ff) :=
by cases b; simp

@[simp] lemma eq_tt_eq_not_eq_ff (b : bool) : (¬(b = ff)) = (b = tt) :=
by cases b; simp

lemma eq_ff_of_not_eq_tt {b : bool} : (¬(b = tt)) → (b = ff) :=
eq.mp (eq_ff_eq_not_eq_tt b)

lemma eq_tt_of_not_eq_ff {b : bool} : (¬(b = ff)) → (b = tt) :=
eq.mp (eq_tt_eq_not_eq_ff b)

@[simp] lemma band_eq_true_eq_eq_tt_and_eq_tt (a b : bool) : (a && b = tt) = (a = tt ∧ b = tt) :=
by cases a; cases b; simp

@[simp] lemma bor_eq_true_eq_eq_tt_or_eq_tt (a b : bool) : (a || b = tt) = (a = tt ∨ b = tt) :=
by cases a; cases b; simp

@[simp] lemma bnot_eq_true_eq_eq_ff (a : bool) : (bnot a = tt) = (a = ff) :=
by cases a; simp

@[simp] lemma band_eq_false_eq_eq_ff_or_eq_ff (a b : bool) : (a && b = ff) = (a = ff ∨ b = ff) :=
by cases a; cases b; simp

@[simp] lemma bor_eq_false_eq_eq_ff_and_eq_ff (a b : bool) : (a || b = ff) = (a = ff ∧ b = ff) :=
by cases a; cases b; simp

@[simp] lemma bnot_eq_ff_eq_eq_tt (a : bool) : (bnot a = ff) = (a = tt) :=
by cases a; simp

@[simp] lemma coe_ff : ↑ff = false :=
show (ff = tt) = false, by simp

@[simp] lemma coe_tt : ↑tt = true :=
show (tt = tt) = true, by simp

@[simp] lemma coe_sort_ff : ↥ff = false :=
show (ff = tt) = false, by simp

@[simp] lemma coe_sort_tt : ↥tt = true :=
show (tt = tt) = true, by simp

@[simp] theorem to_bool_iff (p : Prop) [d : decidable p] : (to_bool p = tt) ↔ p :=
match d with
| is_true hp := ⟨λh, hp, λ_, rfl⟩
| is_false hnp := ⟨λh, bool.no_confusion h, λhp, absurd hp hnp⟩
end

theorem to_bool_true {p : Prop} [decidable p] : p → to_bool p := (to_bool_iff p).2

theorem to_bool_tt {p : Prop} [decidable p] : p → to_bool p = tt := to_bool_true

theorem of_to_bool_true {p : Prop} [decidable p] : to_bool p → p := (to_bool_iff p).1

theorem bool_iff_false {b : bool} : ¬ b ↔ b = ff := by cases b; exact dec_trivial

theorem bool_eq_false {b : bool} : ¬ b → b = ff := bool_iff_false.1

@[simp] theorem to_bool_ff_iff (p : Prop) [decidable p] : to_bool p = ff ↔ ¬p :=
bool_iff_false.symm.trans (not_congr (to_bool_iff _))

theorem to_bool_ff {p : Prop} [decidable p] : ¬p → to_bool p = ff := (to_bool_ff_iff p).2

theorem of_to_bool_ff {p : Prop} [decidable p] : to_bool p = ff → ¬p := (to_bool_ff_iff p).1

theorem to_bool_congr {p q : Prop} [decidable p] [decidable q] (h : p ↔ q) : to_bool p = to_bool q :=
begin
  induction h' : to_bool q,
  exact to_bool_ff (mt h.1 $ of_to_bool_ff h'),
  exact to_bool_true (h.2 $ of_to_bool_true h')
end

@[simp] theorem bor_coe_iff (a b : bool) : a || b ↔ a ∨ b :=
by cases a; cases b; exact dec_trivial

@[simp] theorem band_coe_iff (a b : bool) : a && b ↔ a ∧ b :=
by cases a; cases b; exact dec_trivial

@[simp] theorem bxor_coe_iff (a b : bool) : bxor a b ↔ xor a b :=
by cases a; cases b; exact dec_trivial

@[simp] theorem ite_eq_tt_distrib (c : Prop) [decidable c] (a b : bool) : ((if c then a else b) = tt) = (if c then a = tt else b = tt) :=
by by_cases c; simp [*]

@[simp] theorem ite_eq_ff_distrib (c : Prop) [decidable c] (a b : bool) : ((if c then a else b) = ff) = (if c then a = ff else b = ff) :=
by by_cases c; simp [*]
