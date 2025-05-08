@[simp] def foo (a : Nat) : Nat :=
  2 * a

/--
trace: case h
x : Nat
⊢ 2 * x = x + x
-/
#guard_msgs(all) in
example : foo = fun a => a + a :=
by
  fail_if_success simp -- should not unfold `foo` into a lambda
  funext x
  simp -- unfolds `foo`
  trace_state
  simp +arith

@[simp] def boo : Nat → Nat
  | a => 2 * a

/--
trace: case h
x : Nat
⊢ 2 * x = x + x
-/
#guard_msgs(all) in
example : boo = fun a => a + a :=
by
  fail_if_success simp -- should not unfold `boo` into a lambda
  funext x
  simp -- unfolds `boo`
  trace_state
  simp +arith
