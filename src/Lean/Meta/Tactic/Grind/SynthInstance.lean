/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.SynthInstance
public section
namespace Lean.Meta.Grind
/--
Some modules in grind use builtin instances defined directly in core (e.g., `lia`),
while others synthesize them using `synthInstance` (e.g., `ring`).
This inconsistency is problematic, as it may introduce mismatches and result in
two different representations for the same term.

The following table is used to bypass synthInstance for the builtin cases.
-/
private def builtinInsts : Std.HashMap Expr Expr :=
  let nat := Nat.mkType
  let int := Int.mkType
  let us  := [levelZero, levelZero, levelZero]
  Std.HashMap.ofList [
    (mkApp3 (mkConst ``HAdd us) nat nat nat, Nat.mkInstHAdd),
    (mkApp3 (mkConst ``HSub us) nat nat nat, Nat.mkInstHSub),
    (mkApp3 (mkConst ``HMul us) nat nat nat, Nat.mkInstHMul),
    (mkApp3 (mkConst ``HDiv us) nat nat nat, Nat.mkInstHDiv),
    (mkApp3 (mkConst ``HMod us) nat nat nat, Nat.mkInstHMod),
    (mkApp3 (mkConst ``HPow us) nat nat nat, Nat.mkInstHPow),
    (mkApp  (mkConst ``LT [0]) nat, Nat.mkInstLT),
    (mkApp  (mkConst ``LE [0]) nat, Nat.mkInstLE),

    (mkApp3 (mkConst ``HAdd us) int int int, Int.mkInstHAdd),
    (mkApp3 (mkConst ``HSub us) int int int, Int.mkInstHSub),
    (mkApp3 (mkConst ``HMul us) int int int, Int.mkInstHMul),
    (mkApp3 (mkConst ``HDiv us) int int int, Int.mkInstHDiv),
    (mkApp3 (mkConst ``HMod us) int int int, Int.mkInstHMod),
    (mkApp3 (mkConst ``HPow us) int nat int, Int.mkInstHPow),
    (mkApp  (mkConst ``LT [0]) int, Int.mkInstLT),
    (mkApp  (mkConst ``LE [0]) int, Int.mkInstLE),
  ]

/--
Some modules in grind use builtin instances defined directly in core (e.g., `lia`).
Users may provide nonstandard instances that are definitionally equal to the ones in core.
Given a type, such as `HAdd Int Int Int`, this function returns the instance defined in
core.
-/
def getBuiltinInstance? (type : Expr) : Option Expr :=
  builtinInsts[type]?

def synthInstanceMeta? (type : Expr) : MetaM (Option Expr) := do profileitM Exception "grind typeclass inference" (← getOptions) (decl := type.getAppFn.constName?.getD .anonymous) do
  if let some inst := getBuiltinInstance? type then
    return inst
  catchInternalId isDefEqStuckExceptionId
    (synthInstanceCore? type none)
    (fun _ => pure none)

abbrev synthInstance? (type : Expr) : GoalM (Option Expr) :=
  synthInstanceMeta? type

def synthInstance (type : Expr) : GoalM Expr := do
  let some inst ← synthInstance? type
    | throwError "`grind` failed to find instance{indentExpr type}"
  return inst

/--
Helper function for instantiating a type class `type`, and
then using the result to perform `isDefEq x val`.
-/
def synthInstanceAndAssign (x type : Expr) : GoalM Bool := do
  let some val ← synthInstance? type | return false
  isDefEq x val

end Lean.Meta.Grind
