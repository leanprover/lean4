/-!
# Issue 3922

The `apply?` tactic would apply `symm` to every hypothesis in the local context,
leading to these new hypotheses being included in the term even if they weren't used.
They also created unelaboratable terms such as `?_ (id (r.symm h₂))`.
-/

set_option linter.unusedVariables false

-- set up a binary relation
axiom r : Nat → Nat → Prop

-- that is symmetric
axiom r.symm {a b : Nat} : r a b → r b a

-- and has some other property
axiom r.trans {a b c : Nat} : r a b → r b c → r a c

/--
info: Try this: refine r.symm ?_
---
info: Try this: refine r.trans ?_ ?_
---
warning: declaration uses 'sorry'
-/
#guard_msgs (ordering := sorted) in
example (a b c : Nat) (h₁ : r b a) (h₂ : r b c) : r c a := by
  apply?

-- now attach the `symm` attribute to `r.symm`
attribute [symm] r.symm

/-- info: Try this: exact r.trans (id (r.symm h₂)) h₁ -/
#guard_msgs in
example (a b c : Nat) (h₁ : r b a) (h₂ : r b c) : r c a := by
  apply?
