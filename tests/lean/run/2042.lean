@[simp] def foo (a : Nat) : Nat :=
  2 * a

example : foo = fun a => a + a :=
by
  fail_if_success simp -- should not unfold `foo` into a lambda
  funext x
  simp -- unfolds `foo`
  trace_state
  simp_arith

@[simp] def boo : Nat → Nat
  | a => 2 * a

example : boo = fun a => a + a :=
by
  fail_if_success simp -- should not unfold `boo` into a lambda
  funext x
  simp -- unfolds `boo`
  trace_state
  simp_arith
