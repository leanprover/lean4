/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Simp.SimpM

namespace Lean.Compiler.LCNF
namespace Simp

/--
Try to simplify projections `.proj _ i s` where `s` is constructor.
-/
def simpProj? (e : LetValue) : OptionT SimpM LetValue := do
  let .proj _ i s := e | failure
  let some ctorInfo ← findCtor? s | failure
  match ctorInfo with
  | .ctor ctorVal args => return args[ctorVal.numParams + i]!.toLetValue
  | .natVal .. => failure

/--
Application over application.
```
let g := f a
g b
```
is simplified to `f a b`.
-/
def simpAppApp? (e : LetValue) : OptionT SimpM LetValue := do
  let .fvar g args := e | failure
  let some decl ← findLetDecl? g | failure
  match decl.value with
  | .fvar f args' =>
    /- If `args'` is empty then `g` is an alias that is going to be eliminated by `elimVar?` -/
    guard (!args'.isEmpty)
    return .fvar f (args' ++ args)
  | .const declName us args' => return .const declName us (args' ++ args)
  | .erased => return .erased
  | .proj .. | .value .. => failure

def simpCtorDiscr? (e : LetValue) : OptionT SimpM LetValue := do
  let .const declName _ _ := e | failure
  let some (.ctorInfo _) := (← getEnv).find? declName | failure
  let some fvarId ← simpCtorDiscrCore? e.toExpr | failure
  return .fvar fvarId #[]

def applyImplementedBy? (e : LetValue) : OptionT SimpM LetValue := do
  guard <| (← read).config.implementedBy
  let .const declName us args := e | failure
  let some declNameNew := getImplementedBy? (← getEnv) declName | failure
  return .const declNameNew us args

/-- Try to apply simple simplifications. -/
def simpValue? (e : LetValue) : SimpM (Option LetValue) :=
  -- TODO: more simplifications
  simpProj? e <|> simpAppApp? e <|> simpCtorDiscr? e <|> applyImplementedBy? e
