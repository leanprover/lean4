module

import Lean
import Lean.Compiler.IR.CompilerM

/-!
Interpreter closures carry three hidden arguments in addition to the function's parameters.
Check the largest valid stub through direct evaluation and partial application, and ensure an
oversized stub produces a recoverable `#eval` error (#15977). Synthetic post-lowering IR avoids
elaborating tens of thousands of binders and keeps the runtime parameter count explicit.
-/

open Lean

def interpreterClosureTarget (x : Nat) : Nat := x
def interpreterClosureFactory : Nat := 0

unsafe def testInterpreterClosure (numParams : Nat) (direct : Bool) (fixed : Nat := 0) : CoreM Nat := do
  let env ← getEnv
  let target : IR.Decl := .fdecl `interpreterClosureTarget
    (Array.ofFn fun (i : Fin numParams) => { x := ⟨i.val + 1⟩, borrow := false, ty := .tobject })
    .tobject (.ret (.var ⟨numParams⟩)) { maxVar := numParams, maxJp := 0 }
  let env := IR.declMapExt.addEntry env target
  let opts := (← getOptions).setBool `interpreter.prefer_native false
  if direct then
    discard <| IO.ofExcept <| env.evalConst (Nat → Nat) opts `interpreterClosureTarget false
    return 42
  else
    let args : Array IR.Arg := Array.replicate numParams (.var ⟨1⟩)
    let body : IR.FnBody :=
      .vdecl ⟨1⟩ .tobject (.lit (.num 42)) <|
      .vdecl ⟨2⟩ .object (.pap `interpreterClosureTarget (args.extract 0 fixed)) <|
      .vdecl ⟨3⟩ .tobject (.ap ⟨2⟩ (args.extract fixed numParams)) <|
      .ret (.var ⟨3⟩)
    let factory : IR.Decl := .fdecl `interpreterClosureFactory #[] .tobject body
      { maxVar := 3, maxJp := 0 }
    let env := IR.declMapExt.addEntry env factory
    IO.ofExcept <| env.evalConst Nat opts `interpreterClosureFactory false

/-- info: 42 -/
#guard_msgs in
#eval testInterpreterClosure 4 false

/-- info: 42 -/
#guard_msgs in
#eval testInterpreterClosure 4 false 1

/-- info: 42 -/
#guard_msgs in
#eval testInterpreterClosure 4 true

/-- info: 42 -/
#guard_msgs in
#eval testInterpreterClosure (UInt16.size - 4) false

/-- info: 42 -/
#guard_msgs in
#eval testInterpreterClosure (UInt16.size - 4) false 1

/-- info: 42 -/
#guard_msgs in
#eval testInterpreterClosure (UInt16.size - 4) true

/-- error: cannot create interpreter closure for 'interpreterClosureTarget': 65533 parameters exceed the maximum of 65532 -/
#guard_msgs in
#eval testInterpreterClosure (UInt16.size - 3) false

/-- error: cannot create interpreter closure for 'interpreterClosureTarget': 65533 parameters exceed the maximum of 65532 -/
#guard_msgs in
#eval testInterpreterClosure (UInt16.size - 3) false 1

/-- error: cannot create interpreter closure for 'interpreterClosureTarget': 65533 parameters exceed the maximum of 65532 -/
#guard_msgs in
#eval testInterpreterClosure (UInt16.size - 3) true

/-- info: 42 -/
#guard_msgs in
#eval testInterpreterClosure 4 false
