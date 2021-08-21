def foo (x : Nat) :=
  2*x

def boo (x : Nat) :=
  x + x

@[csimp] theorem foo_eq_boo1 (x : Nat) : foo x = boo x := by -- Error
  simp [foo, boo, Nat.mul_comm]
  show (x * 1) + x = x + x
  simp

@[csimp] theorem foo_eq_boo2 : foo = boo :=
  funext foo_eq_boo1

set_option trace.compiler.ir.init true
def f (x : Nat) : Nat :=
  foo (foo x)
