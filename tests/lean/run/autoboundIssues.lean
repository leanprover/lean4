/-!
# Regression tests for auto-bound implicits
-/

set_option pp.mvars false

/-!
Auto-bound implicit appears in dot notation in the type, for a variable that appears later.
-/
example : n.succ = 1 → n = 0 := by
  intro h; injection h

/-!
Auto-bound implicit appears in dot notation in a binder, for a variable that appears later.
-/
example (h : n.succ = 1) : n = 0 := by
  injection h

/-!
Auto-bound implicit appears as argument to notation that is postponed.
The type of `σ` is specialized to `T` later.
-/
opaque T : Type
opaque T.Pred : T → T → Prop

example {ρ} (hρ : ρ.Pred σ) : T.Pred ρ ρ := sorry


namespace TestRunTermElab
/-!
In the following tests, there is an auto-bound implicit whose type is a metavariable,
which gets turned into an additional variable.
-/

def constUnit (a : A) : Type := Unit

/-!
The auto-bound implicit creates a new variable `A✝`, which comes from the argument name in `constUnit`.
(This has been the case well before the creation of this test.)
-/
/--
trace: A✝ : Sort u_1
a : A✝
_x : constUnit a
⊢ True
-/
#guard_msgs in
example (_x : constUnit a) : True := by
  trace_state
  trivial

variable (x : constUnit a)

/-!
The local context here used to be
```
a✝ : ?_
x✝¹ : constUnit a✝
x✝ : Sort ?_
a : x✝
x : constUnit a
⊢ True
```
Note the duplication and `x✝` for the name of the metavariable-as-a-variable.
The duplication was because `runTermElabM` wasn't resetting the local context.
The poor variable name was due to using `mkForallFVars` instead of `mkForallFVars'`.
-/
/--
trace: A✝ : Sort _
a : A✝
x : constUnit a
⊢ True
-/
#guard_msgs in
example : True := by
  trace_state
  trivial

/-!
Checking that `#check` also has the improvement.
-/
/--
info: 1 : Nat
---
trace: A✝ : Sort _
a : A✝
x : constUnit a
⊢ ?_
-/
#guard_msgs in #check (by trace_state; exact 1)

end TestRunTermElab
