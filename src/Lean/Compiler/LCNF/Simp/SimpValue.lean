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
def simpProj? (e : Expr) : OptionT SimpM Expr := do
  let .proj _ i s := e | failure
  let s ← findCtor s
  let some (ctorVal, args) := s.constructorApp? (← getEnv) | failure
  markSimplified
  return args[ctorVal.numParams + i]!

/--
Application over application.
```
let _x.i := f a
_x.i b
```
is simplified to `f a b`.
-/
def simpAppApp? (e : Expr) : OptionT SimpM Expr := do
  guard e.isApp
  let f := e.getAppFn
  guard f.isFVar
  let f ← findExpr f
  guard <| f.isApp || f.isConst
  guard <| !f.isAppOf ``lcCast
  markSimplified
  return mkAppN f e.getAppArgs

def simpCtorDiscr? (e : Expr) : OptionT SimpM Expr := do
  let some v ← simpCtorDiscrCore? e | failure
  return v

/--
```
let _x.i := lcCast.{u, v} α β a
let _x.j := lcCast.{v, w} β δ _x.i
```
=>
```
let _x.j := lcCast.{u, w} α δ _a
```
-/
def simpCastCast? (e : Expr) : OptionT SimpM Expr := do
  guard <| e.isAppOfArity ``lcCast 3
  let arg ← findExpr e.appArg!
  guard <| arg.isAppOfArity ``lcCast 3
  let δ := e.appFn!.appArg!
  let #[α, _, a] := arg.getAppArgs | unreachable!
  if (← getPhase) matches .base then
    let .const _ [_, w] := e.getAppFn | failure
    let .const _ [u, _] := arg.getAppFn | failure
    return mkAppN (mkConst ``lcCast [u, w]) #[α, δ, a]
  else
    return mkAppN (mkConst ``lcCast) #[α, δ, a]

def applyImplementedBy? (e : Expr) : OptionT SimpM Expr := do
  guard <| (← read).config.implementedBy
  let .const declName us := e.getAppFn | failure
  let some declNameNew := getImplementedBy? (← getEnv) declName | failure
  markSimplified
  return mkAppN (.const declNameNew us) e.getAppArgs

/-- Try to apply simple simplifications. -/
def simpValue? (e : Expr) : SimpM (Option Expr) :=
  -- TODO: more simplifications
  simpProj? e <|> simpAppApp? e <|> simpCtorDiscr? e <|> applyImplementedBy? e <|> simpCastCast? e
