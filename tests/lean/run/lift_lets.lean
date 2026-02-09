/-!
# Tests of the `lift_lets` tactic
-/

set_option linter.unusedVariables false
axiom test_sorry {α : Sort _} : α

/-!
Basic test of let in expression.
-/
/--
trace: ⊢ let x := 1;
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
trace: ⊢ let x := 1;
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
trace: ⊢ let x := 1;
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
Not mergeable, since they must match syntactically.
-/
/--
trace: ⊢ let x := 2;
  let y := 1 + 1;
  x = y
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 1 + 1; y) := by
  lift_lets
  trace_state
  rfl

/-!
Merging with local context.
-/
/--
trace: y : Nat := 1
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
trace: y : Nat := 1
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
trace: ⊢ let y := 1;
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
trace: ⊢ ∀ (n : Nat),
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
trace: ⊢ let x := 0;
  ∀ (n : Nat), n = n + x
-/
#guard_msgs in
example : ∀ n : Nat, n = (let x := 0; n + x) := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Lifting `have` under a binder, dependency.
-/
/--
trace: ⊢ ∀ (n : Nat),
    have x := n;
    n = x
-/
#guard_msgs in
example : ∀ n : Nat, n = (have x := n; x) := by
  lift_lets
  trace_state
  intros
  rfl

/-!
Lifting `have` under a binder, no dependency.
-/
/--
trace: ⊢ have x := 0;
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
trace: ⊢ let y := 1;
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
trace: ⊢ let ty := Nat;
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
error: Tactic `lift_lets` failed: made no progress

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
trace: ⊢ ∀ (n : Nat),
    have x := n;
    x = x
-/
#guard_msgs in
example : ∀ n : Nat, (have x := n; x) = (have x' := n; x') := by
  lift_lets
  trace_state
  intros
  rfl
/--
trace: ⊢ ∀ (n : Nat),
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
trace: ⊢ ∀ (n : Nat),
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
trace: ⊢ ∀ (n : Nat),
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
trace: ⊢ let y := 0;
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
error: Tactic `lift_lets` failed: made no progress

⊢ id = id
-/
#guard_msgs in
example : (id : (let ty := Nat; ty) → Nat) = @id Nat := by
  lift_lets

/-!
Enable lifting from implicit arguments using `+implicit`.
-/
/--
trace: ⊢ let ty := Nat;
  id = id
-/
#guard_msgs in
example : (id : (let ty := Nat; ty) → Nat) = @id Nat := by
  lift_lets +implicits
  trace_state
  rfl

/-!
Lifting at a local hypothesis.
-/
/--
trace: y : Nat
h :
  let x := 1;
  x = y
⊢ True
-/
#guard_msgs in
example (h : (let x := 1; x) = y) : True := by
  lift_lets at h
  trace_state
  trivial

/-!
Lifting in both the type and value for local declarations.
-/
/--
trace: v : let ty := Nat;
id ty :=
  let x := 2;
  id x
⊢ True
-/
#guard_msgs in
example : True := by
  let v : id (let ty := Nat; ty) := id (let x : Nat := 2; x)
  lift_lets at v
  trace_state
  trivial

/-!
Merges using local context, even if the local declaration comes after.
-/
/--
trace: y : Type := Nat
h : y
⊢ True
-/
#guard_msgs in
example (h : let x := Nat; x) : True := by
  let y := Nat
  lift_lets at h
  trace_state
  trivial

/-!
A test to make sure `lift_lets` works after other tactics.
-/
/--
trace: y : Nat
⊢ let x := 1;
  x = y → True
-/
#guard_msgs in
example (h : (let x := 1; x) = y) : True := by
  refine ?_
  revert h
  lift_lets
  trace_state
  intros
  trivial

/-!
Lifting `let`s in proofs in `+proof` mode.
-/
/--
trace: m : Nat
h : ∃ n, n + 1 = m
x : Fin m
y : Fin (h.choose + 1)
⊢ let h' := ⋯;
  cast ⋯ x = y
-/
#guard_msgs in
example (m : Nat) (h : ∃ n, n + 1 = m) (x : Fin m) (y : Fin _) :
    cast (let h' := h.choose_spec.symm; congrArg Fin h') x = y := by
  fail_if_success lift_lets -proofs
  lift_lets +proofs
  trace_state
  exact test_sorry


/-!
### conv mode
-/

/-!
Unlike `extract_lets`, the `lift_lets` conv tactic's modifications persist,
since the local context remains the same.
-/
/--
trace: | let x := Nat;
  x = Int
---
trace: ⊢ let x := Nat;
  x = Int
-/
#guard_msgs in
example : (let x := Nat; x) = Int := by
  conv =>
    lift_lets
    trace_state
  trace_state
  exact test_sorry

/-!
Merging with local context.
-/
/--
trace: y : Type := Nat
| y
---
trace: y : Type := Nat
⊢ y = Int
-/
#guard_msgs in
example : (let x := Nat; x) = Int := by
  let y := Nat
  conv =>
    lhs
    lift_lets
    trace_state
  trace_state
  exact test_sorry
