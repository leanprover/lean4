/-!
# Syntax to create delayed assignment metavariables
-/

/-!
Creating and reusing some synthetic holes using delayed assignment syntax.
-/
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
example : True := by
  let f : Nat → Nat → Nat := fun x y => ?a
  let v := ?a(y := 1, x := 2)

/-!
Error: forward dependencies
-/
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
