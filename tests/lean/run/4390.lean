def step (state: Nat): Option Nat :=
  if state = 0 then none else some (state - 1)

set_option linter.unusedVariables false

def countdown (state: Nat) :=
  match h: step state with
  | none => [state]
  | some newState => state :: countdown newState
termination_by state
decreasing_by sorry

/--
error: tactic 'split' failed, consider using `set_option trace.split.failure true`
state : Nat
p :
  (match h : step state with
    | none => [state]
    | some newState => state :: countdown newState) ≠
    []
⊢ (match h : step state with
        | none => [state]
        | some newState => state :: countdown newState).head
      p =
    state
---
info: [split.failure] `split` tactic failed to generalize discriminant(s) at
      match h : step state with
      | none => [state]
      | some newState => state :: countdown newState
    resulting expression was not type correct
    possible solution: generalize discriminant(s) manually before using `split`
-/
#guard_msgs in
example (state: Nat) (p : (match h : step state with
    | none => [state]
    | some newState => state :: countdown newState) ≠
    []): (match h : step state with
        | none => [state]
        | some newState => state :: countdown newState).head
      p =
    state := by
  set_option trace.split.failure true in
  split

example (state: Nat) (p : (match h : step state with
    | none => [state]
    | some newState => state :: countdown newState) ≠
    []): (match h : step state with
        | none => [state]
        | some newState => state :: countdown newState).head
      p =
    state := by
  split at p <;> simp
