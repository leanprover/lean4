import Lean.Meta.Canonicalizer
import Lean.Elab.Tactic

elab "foo" t:term : tactic => do
  let e ← Lean.Elab.Tactic.elabTerm t none
  trace[debug] "canonicalizing {e}"
  let e' ← (Lean.Meta.canon e).run'
  trace[debug] "canonicalized it to {e'}"

/-- info: ∃ f, ∀ (x : Nat), f x = 0 : Prop -/
#guard_msgs in
#check (∃ f : Nat → Nat, ∀ x, f x = 0) -- works fine

/--
info: [debug] canonicalizing ∃ f, ∀ (x : Nat), f x = 0
[debug] canonicalized it to ∃ f, ∀ (x : Nat), f x = 0
-/
#guard_msgs in
set_option trace.debug true in
example : True := by
  foo (∃ f : Nat → Nat, ∀ x, f x = 0) -- used to fail with "unexpected bound variable #1"
  trivial
