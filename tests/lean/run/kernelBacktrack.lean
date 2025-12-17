/-! Kernel errors (via `Lean.Core.State.snapshotTasks`) should be backtracked. -/

structure Wrapper (α) where val : α

instance {α : Type} [NatCast α] : NatCast (Wrapper α) := sorry

def foo {α : Type} (μ : Wrapper α) (f : α → Nat) : Nat := sorry

macro:max P:term noWs "[" term "]" : term => `(foo $P fun x => 0)

/-! This used to give a kernel error even though there is a succeeding interpretation. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem kernel_error
    (L : List Nat) (hL : L.length = 2 ∧ ∀ i : Fin L.length, L[i] = 0) (i : Nat) :
    L[i % 2] = 0 := sorry

/-- info: 'kernel_error' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in
#print axioms kernel_error
