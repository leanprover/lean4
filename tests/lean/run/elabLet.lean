import Lean
/-!
# Tests of the various `let` options
-/

set_option linter.unusedVariables false

/-!
No options.
-/
/--
info: let x := true;
!x : Bool
-/
#guard_msgs in #check let x := true; !x

/-!
The `+nondep` option gives `have`.
-/
/--
info: have x := true;
!x : Bool
-/
#guard_msgs in #check let +nondep x := true; !x

/-!
The `-nondep` option on `have` is a `let`.
-/
/--
info: let x := true;
!x : Bool
-/
#guard_msgs in #check have -nondep x := true; !x

/-!
The `+zeta` option.
-/
/-- info: !true : Bool -/
#guard_msgs in #check let +zeta x := true; !x

/-!
The `+usedOnly` option.
-/
/--
info: let x := true;
!x : Bool
-/
#guard_msgs in #check let +usedOnly x := true; !x
/-- info: !false : Bool -/
#guard_msgs in #check let +usedOnly x := true; !false

/-!
`eq` for plain `let`
-/
/--
trace: m : Nat := 1
hyp : m = 1
⊢ True
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : True := by
  refine let (eq := hyp) m := 1; ?_
  trace_state
  sorry

/-!
`eq` for `have`
-/
/--
trace: m : Nat
hyp : m = 1
⊢ True
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : True := by
  refine have (eq := hyp) m := 1; ?_
  trace_state
  sorry

/-!
Patterns with `(eq := _)`
-/
/--
trace: p : Nat × Nat
x y : Nat
h : p = (x, y)
this : x + y = p.fst + p.snd
⊢ True
-/
#guard_msgs in
example (p : Nat × Nat) : True :=
  let (eq := h) (x, y) := p
  have : x + y = p.1 + p.2 := by
    simp [h]
  by
    trace_state
    trivial
/--
trace: p : Nat × Nat
x y : Nat
h✝ : p = (x, y)
⊢ x + y = p.fst + p.snd
-/
#guard_msgs in
example (p : Nat × Nat) : True :=
  let (eq := _) (x, y) := p
  have : x + y = p.1 + p.2 := by
    trace_state
    simp [*]
  trivial

/-!
`+postponeValue`, example from `Lean.Elab.Term.Do.ToTerm.mkJoinPoint`.
-/
/--
error: type mismatch
  jp ()
has type
  IO (IO.Ref Bool) : Type
but is expected to have type
  IO Unit : Type
-/
#guard_msgs in
def f (x : Nat) : IO Unit :=
  let jp (u : Unit) : IO _ :=
    IO.mkRef true
  do
    if x > 0 then
      IO.println "not zero"
      jp ()
    else
      jp ()
/--
error: type mismatch
  IO.mkRef true
has type
  BaseIO (IO.Ref Bool) : Type
but is expected to have type
  IO Unit : Type
-/
#guard_msgs in
def f' (x : Nat) : IO Unit :=
  let +postponeValue jp (u : Unit) : IO _ :=
    IO.mkRef true
  do
    if x > 0 then
      IO.println "not zero"
      jp ()
    else
      jp ()

/-!
Testing `+generalize`
-/
/--
trace: x y z : Nat
⊢ z = y + x
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (x y : Nat) : x + y = y + x := by
  refine have +generalize z := x + y; ?_
  trace_state
  sorry
/--
trace: x y z : Nat
h : z = x + y
⊢ z = y + x
-/
#guard_msgs in
example (x y : Nat) : x + y = y + x := by
  refine have +generalize (eq := h) z := x + y; ?_
  trace_state
  rwa [Nat.add_comm] at h

/-!
`+generalize` example with a numeric value.
-/
/--
trace: x y z : Nat
⊢ x ≤ x + z
-/
#guard_msgs in
example (x y : Nat) : x ≤ x + 1 := by
  refine have +generalize z := 1; ?_
  trace_state
  apply Nat.le_add_right

/-!
Motive checking with `+generalize`.
-/
/--
error: failed to elaborate with `+generalize`, generalized expected type is not type correct:
  0 = 0
-/
#guard_msgs in
example (n : Nat) [NeZero n] : (0 : Fin n) = (0 : Fin n) := by
  refine have +generalize z := n; ?_
