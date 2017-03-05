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
