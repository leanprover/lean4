import Lean

/-!
Regression test for #16323: generating `T.ctorIdx` adds no `unsafe` declaration and no
`@[implemented_by]` to a safe inductive type, while the code generator still compiles it to a read
of the constructor tag (see `tests/compile/ctorIdx.lean`).
-/

inductive Test where
  | a
  | b (n : Nat)
  | c (n m : Nat)

inductive Enum where
  | one | two | three

open Lean in
/-- info: [] -/
#guard_msgs in
#eval show CoreM (List Name) from do
  let env ← getEnv
  return env.constants.map₂.toList.filterMap fun (n, info) =>
    if ((``Test).isPrefixOf n || (``Enum).isPrefixOf n) &&
        (info.isUnsafe || (Compiler.getImplementedBy? env n).isSome) then
      some n
    else
      none

/-!
A `casesOn` whose alternatives return literals other than the constructor indices is not compiled
to a read of the tag.
-/

def notCtorIdx (v : Test) : Nat :=
  Test.casesOn (motive := fun _ => Nat) v (nat_lit 1) (fun _ => nat_lit 0) (fun _ _ => nat_lit 2)

/-- info: [1, 0, 2] -/
#guard_msgs in
#eval [Test.a, .b 1, .c 2 3].map notCtorIdx

/-!
A user definition named `ctorIdx`, possible with `genCtorIdx` off, is compiled as written.
-/

set_option genCtorIdx false in
inductive Custom where
  | x | y

def Custom.ctorIdx : Custom → Nat := fun _ => 7

/-- info: [7, 7] -/
#guard_msgs in
#eval [Custom.x, .y].map Custom.ctorIdx
