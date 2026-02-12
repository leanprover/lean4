/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Init.Data
public import Lean.SimpLC
import Lean.Elab.Tactic.Grind

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

-- This possibly could be a simp lemma.
-- It would fire on any `arrow` goal, but we have plenty of these already.
example (x : True → Prop) : (∀ (h : True), x h) ↔ x True.intro :=
  ⟨fun h => h .intro, fun h _ => h⟩
simp_lc allow dite_else_true dite_true

-- Similarly, this could be an `arrow`-indexed simp lemma, but seems very unlikely to be useful.
example (f : α → False) (p : False → Prop) : (∀ (a : α), p (f a)) ↔ True :=
  ⟨fun _ => True.intro, fun _ a => False.elim (f a)⟩
simp_lc allow forall_false forall_apply_eq_imp_iff
simp_lc allow forall_false forall_eq_apply_imp_iff

-- Again, unlikely to be useful.
example (p : α → Prop) (f : α → False) (q : False → Prop) : (∀ (a : α), p a → q (f a)) ↔ True :=
  ⟨fun _ => True.intro, fun _ a _ => False.elim (f a)⟩
simp_lc allow forall_false forall_apply_eq_imp_iff₂

-- Produces many non-confluence goals that could be resolved by better automation.
simp_lc ignore forall_exists_index

-- The following would be easy with some additional automation; indeed `grind` works well.
-- example (q : α → Prop) (a b : α) : q a ∧ b = a ↔ b = a ∧ q b := by
--   grind
simp_lc allow exists_eq_left exists_eq_right_right'
simp_lc allow exists_eq_right exists_eq_left
simp_lc allow exists_eq_right exists_eq_or_imp
simp_lc allow exists_eq_left' exists_eq_right_right'
simp_lc allow exists_eq_right' exists_eq_left'
simp_lc allow exists_eq_right_right exists_eq_left
simp_lc allow exists_eq_right_right exists_eq_left'
simp_lc allow exists_eq_right_right exists_eq_or_imp
simp_lc allow exists_eq_right_right' exists_eq_or_imp

-- These are terrible: they involve different decidable instances
-- (which must all be equal, but the automation doesn't know that).
example {P : Prop} (h h' : Decidable P) :
    ((@decide P h) || (@decide P h')) = ((@decide P h') || (@decide P h)) := by
  have : h = h' := Subsingleton.elim _ _
  -- grind -- works from here
  subst this
  simp
simp_lc allow ite_else_decide_not_self ite_then_decide_not_self
simp_lc allow ite_then_decide_self ite_else_decide_self

-- This would be resolved if `exists_prop'` were a simp lemma, but it is not.
-- See https://github.com/leanprover/lean4/pull/5529
simp_lc allow exists_and_left exists_and_right

-- Can we add:
theorem forall_true (p : True → Prop) : (∀ h : True, p h) ↔ p True.intro :=
  ⟨fun h => h .intro, fun h _ => h⟩
-- Without it we need:
simp_lc allow forall_self_imp forall_apply_eq_imp_iff
simp_lc allow forall_self_imp forall_eq_apply_imp_iff
simp_lc allow forall_self_imp forall_apply_eq_imp_iff₂

-- This is a tricky lemma that removes unused functional dependencies.
-- It causes confluence problems, but is quite useful.
simp_lc ignore forIn'_eq_forIn

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Id _root_
