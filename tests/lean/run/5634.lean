/-!
# Make sure `simpa` checks for metavariables in `using` clause

https://github.com/leanprover/lean4/issues/5634
-/

set_option linter.unnecessarySimpa true

/-!
This used to have a "don't know how to synthesize placeholder" error on the `have` line too.
This is because `have` is `refine_lift have ...; ?_`, so it indeed had a placeholder.
-/
/--
error: don't know how to synthesize placeholder for argument 'a'
context:
htrue : True
⊢ False
---
error: unsolved goals
htrue : True
h✝ : False
⊢ False
-/
#guard_msgs in
example : False := by
  have htrue : True := trivial
  simpa using id _

/-!
Simplified version of the test.
-/
/--
error: don't know how to synthesize placeholder for argument 'a'
context:
⊢ False
---
error: unsolved goals
h✝ : False
⊢ False
-/
#guard_msgs in
example : False := by
  refine ?_
  simpa using id ?_

/-!
Verifying that unassigned metavariables are OK, so long as they come from before elaboring the `using` clause.
-/
example (p : Prop) (h : p) : p := by
  have : ?a := ?b
  simpa using ?b
  exact h

/-!
Occurs check
-/
/--
error: occurs check failed, expression
  ?foo
contains the goal ?foo
-/
#guard_msgs in
example : False := by
  refine ?foo
  simpa using ?foo

/-!
Regression test: need to synthesize postponed metavariables before metavariable checks.
-/
example (α : Type) (x : α) : Nonempty α := by
  simpa using ⟨x⟩

/-!
Regression test: elaborates implicit arguments in the `using` clause
-/
noncomputable example (α : Type) [Nonempty α] : α := by
  simpa using fun {β : Type} [inst : Nonempty β] => Classical.choice inst

/-!
Regression test: elaborates using implicit lambda feature
-/
example (p : Prop) (h : p) : ∀ {_ : Nat}, p := by
  simpa using h

/-!
Regression test: make sure `simpa?` reports lemmas for both the goal and the `using` clause
-/

/-- info: Try this: simpa only [id] using h -/
#guard_msgs in example (p : Prop) (h : p) : id p := by
  simpa? only [id] using h

/-- info: Try this: simpa only [id] using h -/
#guard_msgs in example (p : Prop) (h : id p) : p := by
  simpa? only [id] using h

/-!
Regression test: unnecessary `simpa`
-/

def foo (n : α) := [n]

/--
warning: try 'simp at h' instead of 'simpa using h'
note: this linter can be disabled with `set_option linter.unnecessarySimpa false`
-/
#guard_msgs in
example (h : foo n ≠ [n]) : False := by
  simpa [foo] using h
