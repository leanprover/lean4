/-!
# Syntax to create delayed assignment metavariables
-/

set_option linter.unusedVariables false

/-!
Creating and reusing some synthetic holes using delayed assignment syntax.
-/
/--
info: f : Nat → Nat := fun x => ?a(x)
g : Nat → Nat → Nat := fun x y => ?b(x, y) + ?b(y, x := 1) + ?b(x, y := 1) + ?a(x) + ?a(x := y)
v : Nat := ?b(x := 4, y := 6)
⊢ True

case b
f : Nat → Nat := fun x => ?a(x)
x y : Nat
⊢ Nat

case a
x : Nat
⊢ Nat
---
info: f : Nat → Nat := fun x => ?a(x)
g : Nat → Nat → Nat := fun x y => 3 * x + y + (3 * 1 + y) + (3 * x + 1) + ?a(x) + ?a(x := y)
v : Nat := 3 * 4 + 6
⊢ True

case a
x : Nat
⊢ Nat
---
info: f : Nat → Nat := fun x => x + 2
g : Nat → Nat → Nat := fun x y => 3 * x + y + (3 * 1 + y) + (3 * x + 1) + (x + 2) + (y + 2)
v : Nat := 3 * 4 + 6
⊢ True
-/
#guard_msgs in
example : True := by
  let f : Nat → Nat := fun x => ?a
  let g : Nat → Nat → Nat := fun x y => ?b + ?b(x := 1) + ?b(y := 1) + ?a(x) + ?a(x := y)
  let v := ?b(x := 4, y := 6)
  trace_state
  case b => exact 3 * x + y
  trace_state
  case a => exact x + 2
  trace_state
  trivial

/-!
Error: out of order
-/
/--
error: local variables in delayed assignment syntax must appear in order according to the metavariable's local context:
case a
x y : Nat
⊢ Nat
---
error: unsolved goals
f : Nat → Nat → Nat := fun x y => ?a(x, y)
⊢ True
-/
#guard_msgs in
example : True := by
  let f : Nat → Nat → Nat := fun x y => ?a
  let v := ?a(y := 1, x := 2)

/-!
Error: forward dependencies
-/
/--
error: local variables in delayed assignment syntax must not have forward dependencies in the metavariable's local context:
case a
n : Nat
m : Fin n
⊢ Nat
---
error: unsolved goals
f : (n : Nat) → Fin n → Nat := fun n m => ?a(n, m)
⊢ True
-/
#guard_msgs in
example : True := by
  let f : (n : Nat) → (m : Fin n) → Nat := fun n m => ?a
  let v := ?a(n := 1)

/-!
Using a metavariable later in a different context.
-/
example : (∀ x : Nat, x = x) ∧ (∀ x : Nat, x = x) := by
  refine ⟨fun x => ?a, ?_⟩
  · rfl
  · intro y
    exact ?a(x := y)

/-!
Using the metavariable later in a different context, in the same term.
-/
example : (∀ x : Nat, x = x) ∧ (∀ x : Nat, x = x) := by
  refine ⟨fun x => ?a(x), fun x => ?a(x)⟩
  · rfl
