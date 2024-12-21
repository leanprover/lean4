/-!
# Tests of the `lift_lets` tactic
-/

set_option linter.unusedVariables false
axiom test_sorry {α : Sort _} : α

/-!
Basic test of let in expression.
-/
/--
info: ⊢ let x := 1;
  x = 1
-/
#guard_msgs in
example : (let x := 1; x) = 1 := by
  lift_lets
  trace_state
  intro
  rfl

/-!
Merging
-/
/--
info: ⊢ let x := 1;
  x = x
-/
#guard_msgs in
example : (let x := 1; x) = (let y := 1; y) := by
  lift_lets
  trace_state
  intro
  rfl

/-!
Merging off.
-/
/--
info: ⊢ let x := 1;
  let y := 1;
  x = y
-/
#guard_msgs in
example : (let x := 1; x) = (let y := 1; y) := by
  lift_lets -merge
  trace_state
  intros
  rfl

/-!
Merging with local context.
-/
/--
info: y : Nat := 1
⊢ y = 1
-/
#guard_msgs in
example : (let x := 1; x) = 1 := by
  let y := 1
  lift_lets
  trace_state
  rfl

/-!
Merging with local context, for top-level.
-/
/--
info: y : Nat := 1
⊢ y = 1
-/
#guard_msgs in
example : let x := 1; x = 1 := by
  let y := 1
  lift_lets
  trace_state
  rfl

/-!
Recursive lifting
-/
/--
info: ⊢ let y := 1;
  let x := y + 1;
  x + 1 = 3
-/
#guard_msgs in
example : (let x := (let y := 1; y + 1); x + 1) = 3 := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Lifting under a binder, dependency.
-/
/--
info: ⊢ ∀ (n : Nat),
    let x := n;
    n = x
-/
#guard_msgs in
example : ∀ n : Nat, n = (let x := n; x) := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Lifting under a binder, no dependency.
-/
/--
info: ⊢ let x := 0;
  ∀ (n : Nat), n = n + x
-/
#guard_msgs in
example : ∀ n : Nat, n = (let x := 0; n + x) := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Lifting `letFun` under a binder, dependency.
-/
/--
info: ⊢ ∀ (n : Nat),
    let_fun x := n;
    n = x
-/
#guard_msgs in
example : ∀ n : Nat, n = (have x := n; x) := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Lifting `letFun` under a binder, no dependency.
-/
/--
info: ⊢ let_fun x := 0;
  ∀ (n : Nat), n = n + x
-/
#guard_msgs in
example : ∀ n : Nat, n = (have x := 0; n + x) := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Recursive lifting, one of the internal lets can leave the binder.
-/
/--
info: ⊢ let y := 1;
  (fun x =>
        let a := x;
        a + y)
      2 =
    2 + 1
-/
#guard_msgs in
example : (fun x => let a := x; let y := 1; a + y) 2 = 2 + 1 := by
  lift_lets
  trace_state
  intro
  rfl

/-!
Lifting out of binder type.
-/
/--
info: ⊢ let ty := Nat;
  (fun x => Nat) 2
-/
#guard_msgs in
example : (fun (_ : let ty := Nat; ty) => Nat) (2 : Nat) := by
  lift_lets
  trace_state
  exact 0

/-!
When `-types`, doesn't lift out of binder type.
-/
/--
error: tactic 'lift_lets' failed, made no progress
⊢ (fun x => Nat) 2
-/
#guard_msgs in
example : (fun (_ : let ty := Nat; ty) => Nat) (2 : Nat) := by
  lift_lets -types

/-!
Merging of lets of different kinds.
Four cases to this test, depending on whether a `have` or `let` is seen first,
and whether the second is a `have` or `let`.
-/
/--
info: ⊢ ∀ (n : Nat),
    let_fun x := n;
    x = x
-/
#guard_msgs in
example : ∀ n : Nat, (have x := n; x) = (have x' := n; x') := by
  lift_lets
  trace_state
  intros
  rfl
/--
info: ⊢ ∀ (n : Nat),
    let x := n;
    x = x
-/
#guard_msgs in
example : ∀ n : Nat, (let x := n; x) = (have x' := n; x') := by
  lift_lets
  trace_state
  intros
  rfl
/--
info: ⊢ ∀ (n : Nat),
    let x := n;
    x = x
-/
#guard_msgs in
example : ∀ n : Nat, (have x := n; x) = (let x' := n; x') := by
  lift_lets
  trace_state
  intros
  rfl
/--
info: ⊢ ∀ (n : Nat),
    let x := n;
    x = x
-/
#guard_msgs in
example : ∀ n : Nat, (let x := n; x) = (let x' := n; x') := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Make sure it doesn't lift things that transitively depend on a binder.
-/
example : ∀ n : Nat, let x := n; let y := x; y = n := by
  fail_if_success lift_lets
  intros
  rfl

/-!
Lifting from underneath an unliftable let is OK.
-/
/--
info: ⊢ let y := 0;
  ∀ (n : Nat),
    let x := n;
    x + y = n
-/
#guard_msgs in
example : ∀ n : Nat, let x := n; let y := 0; x + y = n := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Doesn't lift from implicit arguments by default
-/
/--
error: tactic 'lift_lets' failed, made no progress
⊢ id = id
-/
#guard_msgs in
example : (id : (let ty := Nat; ty) → Nat) = @id Nat := by
  lift_lets

/-!
Enable lifting from implicit arguments using `+implicit`.
-/
/--
info: ⊢ let ty := Nat;
  id = id
-/
#guard_msgs in
example : (id : (let ty := Nat; ty) → Nat) = @id Nat := by
  lift_lets +implicits
  trace_state
  rfl

example (h : )

/-!
Merges using local context, even the local declaration comes after.
-/
/--
info: y : Type := Nat
h : y
⊢ True
-/
#guard_msgs in
example (h : let x := Nat; x) : True := by
  let y := Nat
  lift_lets at h
  trace_state
  trivial

example : (x : let ty := Nat; ty) → let y := (1 : Nat); Fin (y + Nat.succ x) := by
  lift_lets
  guard_target =ₛ let ty := Nat; let y := 1; (x : ty) → Fin (y + Nat.succ x)
  intro ty y x
  rw [Nat.add_succ, Nat.succ_eq_add_one]
  exact 0

example : (x : Nat) → (y : Nat) → let z := x + 1; let w := 3; Fin (z + w) := by
  lift_lets
  guard_target =ₛ let w := 3; (x : Nat) → let z := x + 1; Nat → Fin (z + w)
  intro w x z _y
  simp [w, z]
  exact 0

example : (x : Nat) → let z := x + 1; (y : Nat) → let w := 3; Fin (z + w) := by
  lift_lets
  guard_target =ₛ let w := 3; (x : Nat) → let z := x + 1; Nat → Fin (z + w)
  intro w x z _y
  simp [w, z]
  exact 0

example : (let x := 1; x) = (let x := 1; x) := by
  lift_lets
  guard_target =ₛ let x := 1; x = x
  rfl

example : (let x := 2; x) = (let y := 1; y + 1) := by
  lift_lets
  guard_target =ₛ let x := 2; let y := 1; x = y + 1
  rfl

example (h : (let x := 1; x) = y) : True := by
  lift_lets at h
  guard_hyp h :ₛ let x := 1; x = y
  trivial

example (h : (let x := 1; x) = y) : True := by
  revert h
  lift_lets
  intro x h
  guard_hyp x : Nat := 1
  guard_hyp h :ₛ x = y
  trivial

example : let x := 1; ∀ n, let y := 1; x + n = y + n := by
  lift_lets
  guard_target =ₛ let x := 1; ∀ n, x + n = x + n
  intros x n
  rfl

example (m : Nat) (h : ∃ n, n + 1 = m) (x : Fin m) (y : Fin _) :
    cast (let h' := h.choose_spec.symm; congrArg Fin h') x = y := by
  lift_lets (config := {proofs := true})
  intro h'
  exact test_sorry


/-!
### conv mode
-/
