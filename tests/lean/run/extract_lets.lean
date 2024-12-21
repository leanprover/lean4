/-!
# Tests of the `extract_lets` tactic
-/

set_option linter.unusedVariables false
axiom test_sorry {α : Sort _} : α

/-!
Extract a top-level let, no names given.
-/
/--
info: x✝ : Nat := 2
⊢ x✝ = 2
-/
#guard_msgs in
example : let x := 2; x = 2 := by
  extract_lets
  trace_state
  rfl

/-!
Extract a top-level let, name given.
-/
/--
info: z : Nat := 2
⊢ z = 2
-/
#guard_msgs in
example : let x := 2; x = 2 := by
  extract_lets z
  trace_state
  rfl

/-!
Extract a top-level let, placeholder name given.
-/
/--
info: x✝ : Nat := 2
⊢ x✝ = 2
-/
#guard_msgs in
example : let x := 2; x = 2 := by
  extract_lets _
  trace_state
  rfl

/-!
Extract an embedded let, name given.
-/
/--
info: z : Nat := 2
⊢ z = 2
-/
#guard_msgs in
example : (let x := 2; x) = 2 := by
  extract_lets z
  trace_state
  rfl

/-!
Extract multiple embedded lets, no names given.
-/
/--
info: x✝ : Nat := 2
y✝ : Nat := 1 + 1
⊢ x✝ = y✝
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 1 + 1; y) := by
  extract_lets
  trace_state
  rfl

/-!
Length of name list controls number of lets.
-/
/--
info: z : Nat := 2
⊢ z =
    let y := 1 + 1;
    y
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 1 + 1; y) := by
  extract_lets z
  trace_state
  rfl
/--
info: z : Nat := 2
w : Nat := 1 + 1
⊢ z = w
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 1 + 1; y) := by
  extract_lets z w
  trace_state
  rfl

/-!
Ellipsis
-/
/--
info: z : Nat := 2
y✝ : Nat := 1 + 1
⊢ z = y✝
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 1 + 1; y) := by
  extract_lets z ..
  trace_state
  rfl

/-!
Merging.
-/
/--
info: x✝ : Nat := 2
⊢ x✝ = x✝
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 2; y) := by
  extract_lets
  trace_state
  rfl

/-!
Merging, even if we run out of names.
-/
/--
info: z : Nat := 2
⊢ z = z
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 2; y) := by
  extract_lets z
  trace_state
  rfl

/-!
Merging reuses pre-existing declarations
-/
/--
info: z : Nat := 2
⊢ z = z
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 2; y) := by
  let z := 2
  extract_lets
  trace_state
  rfl

/-!
Merging doesn't reuse pre-existing declarations when `-useContext`.
-/
/--
info: z : Nat := 2
x✝ : Nat := 2
⊢ x✝ = x✝
-/
#guard_msgs in
example : (let x := 2; x) = (let y := 2; y) := by
  let z := 2
  extract_lets -useContext
  trace_state
  rfl

/-!
Works with `have` (`let_fun`)
-/
/--
info: a✝ : Nat := 2
x✝ : Nat := a✝
y✝ : Nat := a✝ + 0
⊢ x✝ = y✝
-/
#guard_msgs in
example : have a := 2; (have x := a; x) = (have y := a + 0; y) := by
  extract_lets
  trace_state
  rfl

/-!
Extracts at both the type and the value of a local definition.
-/
/--
info: α✝ : Type := Nat
y✝ : Nat := 2
x : α✝ := 2
⊢ x = x
-/
#guard_msgs in
example : let x : (let α := Nat; α) := (let y := 2; 2); x = x := by
  intro x
  extract_lets at x
  trace_state
  rfl
-- Essentially same state:
/--
info: α✝ : Type := Nat
y✝ : Nat := 2
x✝ : α✝ := 2
⊢ x✝ = x✝
-/
#guard_msgs in
example : let x : (let α := Nat; α) := (let y := 2; 2); x = x := by
  extract_lets
  trace_state
  rfl

/-!
Basic `descend := false` test.
-/
/--
info: x✝ : Nat := 2
⊢ x✝ = 2
-/
#guard_msgs in
example : let x := 2; x = 2 := by
  extract_lets -descend
  trace_state
  rfl

/-!
Make sure `descend := false` is not obstructed by metadata.
-/
/--
info: this : True
x✝ : Nat := 2
⊢ x✝ = 2
-/
#guard_msgs in
example : let x := 2; x = 2 := by
  have : True := trivial
  extract_lets -descend
  trace_state
  rfl

/-
In `-descend` mode, does not extract embedded let.
-/
/--
error: tactic 'extract_lets' failed, nothing to extract
⊢ (let x := 2;
    x) =
    2
-/
#guard_msgs in
example : (let x := 2; x) = 2 := by
  extract_lets -descend z

/-!
In `-descend` mode, merges using pre-existing declarations.
-/
/--
info: w : Nat := 2
y✝ : Nat := 3
⊢ w = 2 + y✝ - y✝
-/
#guard_msgs in
example : let x := 2; let y := 3; let z := 3; x = 2 + y - z := by
  let w := 2
  extract_lets -descend
  trace_state
  rfl

/-!
`-descend` works with `have` (`let_fun`)
-/
/--
info: a✝ : Nat := 2
⊢ (let_fun x := a✝;
    x) =
    let_fun y := a✝ + 0;
    y
-/
#guard_msgs in
example : have a := 2; (have x := a; x) = (have y := a + 0; y) := by
  extract_lets -descend
  trace_state
  rfl

/-!
Extracting at a hypothesis
-/
/--
info: x✝ : Nat := 1
h : x✝ = x✝
⊢ True
-/
#guard_msgs in
example (h : let x := 1; x = x) : True := by
  extract_lets at h
  fail_if_success extract_lets a at h
  trace_state
  trivial

/-!
Extracting at a hypothesis, with names
-/
/--
info: y : Nat := 1
h : y = y
⊢ True
-/
#guard_msgs in
example (h : let x := 1; x = x) : True := by
  extract_lets y at h
  fail_if_success extract_lets a at h
  trace_state
  trivial

/-!
Extracting at a hypothesis, reorders hypotheses
-/
/--
info: h' : Nat
y : Nat := 1
h : y = y
⊢ True
-/
#guard_msgs in
example (h : let x := 1; x = x) (h' : Nat) : True := by
  extract_lets y at h
  fail_if_success extract_lets a at h
  trace_state
  trivial

/-!
Extracting at a hypothesis, not all top level.
-/
/--
info: x✝ : Nat := 1
y✝ : Nat := 2
h : x✝ + 1 = y✝
⊢ True
-/
#guard_msgs in
example (h : let x := 1; x + 1 = let y := 2; y) : True := by
  extract_lets at h
  trace_state
  trivial

/-!
Extracting at a hypothesis, not all top level, in `-descend` mode.
-/
/--
info: x✝ : Nat := 1
h :
  x✝ + 1 =
    let y := 2;
    y
⊢ True
-/
#guard_msgs in
example (h : let x := 1; x + 1 = let y := 2; y) : True := by
  extract_lets -descend at h
  trace_state
  trivial

/-!
At multiple locations with `merge := true`.
-/
/--
info: _z✝ : Nat := 3
x✝ : Nat := 1
h : x✝ + 2 = _z✝
⊢ Nat → True
-/
#guard_msgs in
example (h : let x := 1; let y := 3; x + 2 = y) : let _z := 3; ∀ (_ : Nat), True := by
  extract_lets at *
  trace_state
  intro
  trivial

/-!
At multiple locations with `merge := false`.
-/
/--
info: _z✝ : Nat := 3
x✝ : Nat := 1
y✝ : Nat := 3
h : x✝ + 2 = y✝
⊢ Nat → True
-/
#guard_msgs in
example (h : let x := 1; let y := 3; x + 2 = y) : let _z := 3; ∀ (_ : Nat), True := by
  extract_lets -merge at *
  trace_state
  intro
  trivial

/-!
Merging can chain. This tests how extracted let declarations are recalled and can handle dependence.
-/
/--
info: x✝ : Nat := 2
y✝ : Nat := x✝
⊢ y✝ = y✝
-/
#guard_msgs in
example : (let x := 2; let y := x; y) = (let x' := 2; let y' := x'; y') := by
  extract_lets
  trace_state
  rfl

/-!
Same merging example, but with `-merge`.
-/
/--
info: x✝ : Nat := 2
y✝ : Nat := x✝
x'✝ : Nat := 2
y'✝ : Nat := x'✝
⊢ y✝ = y'✝
-/
#guard_msgs in
example : (let x := 2; let y := x; y) = (let x' := 2; let y' := x'; y') := by
  extract_lets -merge
  trace_state
  rfl

/-!
This tests an issue reported about the mathlib version of `extract_lets`.
Reported at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60extract_lets.60.20fails.20in.20a.20hypothesis.20if.20the.20name.20is.20unused/near/439675718
Unused lets are handled properly.
-/
/--
info: ok✝ : Prop := True
h :
  let _not_ok := False;
  ok✝
⊢ let _also_ok := 3;
  True
---
info: ok✝ : Prop := True
h :
  let _not_ok := False;
  ok✝
_also_ok✝ : Nat := 3
⊢ True
---
info: ok✝ : Prop := True
_also_ok✝ : Nat := 3
_not_ok✝ : Prop := False
h : ok✝
⊢ True
-/
#guard_msgs in
example (h : let ok := True; let _not_ok := False; ok) : let _also_ok := 3; True := by
  extract_lets _ at h
  trace_state
  extract_lets _
  trace_state
  extract_lets _ at h
  trace_state
  trivial

/-!
Testing `+usedOnly`
-/
/--
info: ok✝ : Prop := True
h : ok✝
⊢ let _also_ok := 3;
  True
---
info: ok✝ : Prop := True
h : ok✝
⊢ True
-/
#guard_msgs in
example (h : let ok := True; let _not_ok := False; ok) : let _also_ok := 3; True := by
  extract_lets +usedOnly _ at h
  trace_state
  extract_lets +usedOnly _
  trace_state
  trivial

/-!
Testing `+usedOnly` with `-descend`
-/
/--
info: ok✝ : Prop := True
h : ok✝
⊢ let _also_ok := 3;
  True
---
info: ok✝ : Prop := True
h : ok✝
⊢ True
-/
#guard_msgs in
example (h : let ok := True; let _not_ok := False; ok) : let _also_ok := 3; True := by
  extract_lets -descend +usedOnly _ at h
  trace_state
  extract_lets -descend +usedOnly _
  trace_state
  trivial

/-!
`+proofs`
-/
/--
info: this✝ : (some true).isSome = true := of_eq_true (eq_self true)
⊢ (some true).get this✝ = true
-/
#guard_msgs in
example : Option.get (some true) (have := (by simp); this) = true := by
  fail_if_success extract_lets -proofs
  extract_lets +proofs
  trace_state
  rfl

/-!
`+implicits`
-/
/--
info: α✝ : Type := Nat
⊢ id 2 = 2
-/
#guard_msgs in
example : @id (let α := Nat; α) 2 = 2 := by
  fail_if_success extract_lets -implicits
  extract_lets +implicits
  trace_state
  rfl

/-!
`-types`, works both to inhibit when the top level is a type and when the subterm is a type.
(This option isn't so useful outside of `conv` mode.)
-/
example : (let x := Nat; x) = Nat := by
  fail_if_success extract_lets -types
  extract_lets +types
  rfl
example : (let x := 2; x) = 2 := by
  fail_if_success extract_lets -types
  extract_lets +types
  rfl

/-!
Let value depends on binder, fails.
-/
example : ∀ n : Nat, let x := n; x = x := by
  fail_if_success extract_lets
  intros
  rfl

/-!
Can extract from underneath another `let`.
-/
/--
info: y✝ : Nat := 2
⊢ ∀ (n : Nat),
    let x := n;
    x + y✝ = x + y✝
-/
#guard_msgs in
example : ∀ n : Nat, let x := n; let y := 2; x + y = x + y := by
  extract_lets
  trace_state
  intros
  rfl

/-!
Can't extract from underneath another `let` when `underBinder := false`.
-/
/--
error: tactic 'extract_lets' failed, nothing to extract
⊢ ∀ (n : Nat),
    let x := n;
    let y := 2;
    x + y = x + y
-/
#guard_msgs in
example : ∀ n : Nat, let x := n; let y := 2; x + y = x + y := by
  extract_lets -underBinder

/-!
### Conv mode
-/

/-!
Limitation: we can use `extract_lets` within `conv`, but the let bindings do not persist.
-/
/--
info: y : Type := Nat
| y = Int
---
info: ⊢ Nat = Int
-/
#guard_msgs in
example : let x := Nat; x = Int := by
  conv =>
    extract_lets y
    trace_state
  trace_state
  exact test_sorry
