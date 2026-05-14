import Lean

/-! Test for the `Command.State.newDecls` mechanism.

Defines a local `#print_new_decls` command that elaborates a nested command
and reports the names of declarations added during its elaboration.
Exercises the def, mutual, inductive, and theorem paths.
-/

open Lean Elab Command

elab "#print_new_decls " cmd:command : command => do
  let before ← getNewDecls
  elabCommand cmd
  let after ← getNewDecls
  let added := after.extract before.size after.size
  logInfo m!"new declarations: {added.toList}"

/-- info: new declarations: [foo] -/
#guard_msgs in
#print_new_decls def foo : Nat := 42

/-- info: new declarations: [bar, baz] -/
#guard_msgs in
#print_new_decls
mutual
  def bar : Nat := 1
  def baz : Nat := 2
end

/--
info: new declarations: [Color,
 Color.rec,
 Color.red,
 Color.green,
 Color.blue,
 Color.recOn,
 Color.casesOn,
 Color.ctorIdx,
 Color.toCtorIdx,
 Color.ctorElimType,
 Color.ctorElim,
 Color.red.elim,
 Color.green.elim,
 Color.blue.elim,
 Color.noConfusionType,
 Color.noConfusion,
 Color._sizeOf_1,
 Color._sizeOf_inst,
 Color.red.sizeOf_spec,
 Color.green.sizeOf_spec,
 Color.blue.sizeOf_spec]
-/
#guard_msgs in
#print_new_decls
inductive Color where
  | red
  | green
  | blue

/-- info: new declarations: [pythagoras] -/
#guard_msgs in
#print_new_decls
theorem pythagoras (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- info: new declarations: [_example] -/
#guard_msgs in
#print_new_decls example : True := trivial
