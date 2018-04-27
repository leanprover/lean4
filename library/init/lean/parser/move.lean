/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.data
import init.meta.mk_dec_eq_instance

-- non-meta instance
attribute [derive decidable_eq] name

universes u v w

namespace name
  @[simp] protected def quick_lt : name → name → Prop
  | anonymous        anonymous          := false
  | anonymous        _                  := true
  | (mk_numeral v n) (mk_numeral v' n') := v < v' ∨ v = v' ∧ n.quick_lt n'
  | (mk_numeral _ _) (mk_string _ _)    := true
  | (mk_string s n)  (mk_string s' n')  := s < s' ∨ s = s' ∧ n.quick_lt n'
  | _                _                  := false

  instance decidable_rel_quick_lt : decidable_rel name.quick_lt :=
  begin
    intros n n',
    induction n generalizing n',
    case anonymous {
      by_cases n' = anonymous; simp *; apply_instance
    },
    all_goals { cases n'; {
      tactic.unfreeze_local_instances, -- use recursive instance
      simp; apply_instance } }
  end

  protected def has_lt_quick : has_lt name := ⟨name.quick_lt⟩
end name

namespace option
  variables {α : Type u} (r : α → α → Prop)

  @[simp] protected def lt : option α → option α → Prop
  | none (some x) := true
  | (some x) (some y) := r x y
  | _ _ := false

  instance decidable_rel_lt [decidable_rel r] : decidable_rel (option.lt r) :=
  by intros a b; cases a; cases b; simp; apply_instance

  protected def has_lt [has_lt α] : has_lt (option α) := ⟨option.lt (<)⟩
end option
