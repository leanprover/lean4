import Lean
open Lean Compiler LCNF
@[noinline] def double (x : Nat) := x + x

set_option pp.funBinderTypes true
set_option trace.Compiler.result true in
def g (n : Nat) (a b : α) (f : α → α) :=
  match n with
  | 0 => a
  | n+1 => f (g n a b f)

set_option trace.Compiler.result true in
def h (n : Nat) (a : Nat) :=
  g n a a double + g a n n double
