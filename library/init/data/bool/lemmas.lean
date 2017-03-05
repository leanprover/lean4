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
