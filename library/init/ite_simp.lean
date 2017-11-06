/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.bool

/-
Simplification lemmas for ite.

We don't prove them at logic.lean because it is easier to prove them using
the tactic framework.
-/

@[simp] lemma if_true_right_eq_or (p : Prop) [h : decidable p] (q : Prop) : (if p then q else true) = (¬p ∨ q) :=
by by_cases p; simp [h]

@[simp] lemma if_true_left_eq_or (p : Prop) [h : decidable p] (q : Prop) : (if p then true else q) = (p ∨ q) :=
by by_cases p; simp [h]

@[simp] lemma if_false_right_eq_and (p : Prop) [h : decidable p] (q : Prop) : (if p then q else false) = (p ∧ q) :=
by by_cases p; simp [h]

@[simp] lemma if_false_left_eq_and (p : Prop) [h : decidable p] (q : Prop) : (if p then false else q) = (¬p ∧ q) :=
by by_cases p; simp [h]
