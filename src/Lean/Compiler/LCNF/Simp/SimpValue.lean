/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Simp.SimpM

public section

namespace Lean.Compiler.LCNF
namespace Simp

/--
Try to simplify projections `.proj _ i s` where `s` is constructor.
-/
def simpProj? (e : LetValue .pure) : OptionT SimpM (LetValue .pure) := do
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
def simpAppApp? (e : LetValue .pure) : OptionT SimpM (LetValue .pure) := do
  let .fvar g args := e | failure
  let some decl ← findLetDecl? g | failure
  match decl.value with
  | .fvar f args' =>
    /- If `args` is empty then `g` is an alias that is going to be eliminated by `elimVar?` -/
    guard (!args.isEmpty)
    return .fvar f (args' ++ args)
  | .const declName us args' =>
    /- If `args` is empty then `g` is an alias that is going to be eliminated by `elimVar?` -/
    guard (!args.isEmpty)
    return .const declName us (args' ++ args)
  | .erased => return .erased
  | .proj .. | .lit .. => failure

def simpCtorDiscr? (e : LetValue .pure) : OptionT SimpM (LetValue .pure) := do
  let .const declName _ args := e | failure
  /-
  Don't replace scalar constructors like `true` / `false` in the first pass to avoid the following
  kind of situation (which occurred e.g. in the `charactersIn` benchmark):
  1. `instDecidableEqBool x true` gets converted to `instDecidableEqBool x y` by this function
  2. `pullFunDecls` moves `instDecidableEqBool x y` into a place where `y` is no longer known
     to be `true`
  3. `instDecidableEqBool` is inlined as usual, producing an unnecessary branch on `y`
  -/
  if !(← read).config.simpCtor && args.isEmpty then failure
  let some (.ctorInfo _) := (← getEnv).find? declName | failure
  let some fvarId ← simpCtorDiscrCore? e.toExpr | failure
  return .fvar fvarId #[]

def applyImplementedBy? (e : LetValue .pure) : OptionT SimpM (LetValue .pure) := do
  guard <| (← read).config.implementedBy
  let .const declName us args := e | failure
  let some declNameNew := getImplementedBy? (← getEnv) declName | failure
  return .const declNameNew us args

/-- Try to apply simple simplifications. -/
def simpValue? (e : LetValue .pure) : SimpM (Option (LetValue .pure)) :=
  -- TODO: more simplifications
  simpProj? e <|> simpAppApp? e <|> simpCtorDiscr? e <|> applyImplementedBy? e
