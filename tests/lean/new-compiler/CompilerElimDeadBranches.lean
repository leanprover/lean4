def someVal (_x : Nat) : Option Nat := some 0

/-
This test demonstrates two things:
1. We eliminate all branches except the some, some one
2. We communicate correctly to the constant folder that the `n` and `m`
   are always 0 and can thus collapse the computation.
-/
set_option trace.Compiler.elimDeadBranches true in
set_option trace.Compiler.result true in
def addSomeVal (x : Nat) :=
  match someVal x, someVal x with
  | some n, some m => some (n + m)
  | _, _ => none


def throwMyError (m n : Nat) : Except String Unit :=
  throw s!"Ahhhh {m + n}"

/-
This demonstrates that the optimization does do good things to monadic
code. In this snippet Lean would usually perform a cases on the result
of `throwMyError` in order to figure out whether it has to:
- raise an error and exit right now
- jump to the the `return x + y` continuation
Since the abstract interpreter knows that `throwMyError` always returns
an `Except.error` it will drop the branch where we jump to the continuation.
This will in turn allow the simplifier to drop the join point that represents
the continuation, saving us more code size.
-/
set_option trace.Compiler.elimDeadBranches true in
set_option trace.Compiler.result true in
def monadic (x y : Nat) : Except String Nat := do
  if let some m := addSomeVal x then
    if let some n := addSomeVal y then
      throwMyError m n
  return x + y
