import Simplc

-- This possibly could be a simp lemma. It would fire on any `arrow` goal, but we have plenty of these already.
example (x : True → Prop) : (∀ (h : True), x h) ↔ x True.intro :=
  ⟨fun h => h .intro, fun h _ => h⟩
simp_lc whitelist dite_else_true dite_true

-- Similarly, this could be an `arrow`-indexed simp lemma, but seems very unlikely to be useful.
example (f : α → False) (p : False → Prop) : (∀ (a : α), p (f a)) ↔ True :=
  ⟨fun _ => True.intro, fun _ a => False.elim (f a)⟩
simp_lc whitelist forall_false forall_apply_eq_imp_iff
simp_lc whitelist forall_false forall_eq_apply_imp_iff

-- Again, unlikely to be useful.
example (p : α → Prop) (f : α → False) (q : False → Prop) : (∀ (a : α), p a → q (f a)) ↔ True :=
  ⟨fun _ => True.intro, fun _ a _ => False.elim (f a)⟩
simp_lc whitelist forall_false forall_apply_eq_imp_iff₂

-- Produces many non-confluence goals that could be resolved by better automation.
simp_lc ignore forall_exists_index

-- All easy with some additional automation.
simp_lc whitelist exists_eq_left exists_eq_right_right'
simp_lc whitelist exists_eq_right exists_eq_left
simp_lc whitelist exists_eq_right exists_eq_or_imp
simp_lc whitelist exists_eq_left' exists_eq_right_right'
simp_lc whitelist exists_eq_right' exists_eq_left'
simp_lc whitelist exists_eq_right_right exists_eq_left
simp_lc whitelist exists_eq_right_right exists_eq_left'
simp_lc whitelist exists_eq_right_right exists_eq_or_imp
simp_lc whitelist exists_eq_right_right' exists_eq_or_imp

-- These are terrible: they involve different decidable instances (which must all be equal, but the automation doesn't know that).
example {P : Prop} (h h' : Decidable P) : ((@decide P h) || (@decide P h')) = ((@decide P h') || (@decide P h)) := by
  have : h = h' := Subsingleton.elim _ _
  subst this
  simp
simp_lc whitelist ite_else_decide_not_self ite_then_decide_not_self
simp_lc whitelist ite_then_decide_self ite_else_decide_self

-- This would be resolved if `exists_prop'` were a simp lemma, but it is not.
-- See https://github.com/leanprover/lean4/pull/5529
simp_lc whitelist exists_and_left exists_and_right

example (x : Id PUnit) : PUnit.unit = x := by
  change PUnit at x
  simp
simp_lc whitelist Id.bind_eq bind_pure_unit

#guard_msgs (drop info) in
simp_lc check in Id _root_
