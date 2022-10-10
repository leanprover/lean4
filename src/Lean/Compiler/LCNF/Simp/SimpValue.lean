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
  return args[ctorVal.numParams + i]!

/--
Return `some type` if `f args` is type correct, and has type `type`.
-/
def checkApp? (f : Expr) (args : Array Expr) : CompilerM (Option Expr) := do
  let mut fType ← inferType f
  let mut j := 0
  for i in [:args.size] do
    let arg := args[i]!
    if fType.isErased then
      return fType
    fType := fType.headBeta
    let (d, b) ←
      match fType with
      | .forallE _ d b _ => pure (d, b)
      | _ =>
        fType := fType.instantiateRevRange j i args |>.headBeta
        match fType with
        | .forallE _ d b _ => j := i; pure (d, b)
        | _ =>
          if fType.isErased then return fType
          return none
    let argType ← inferType arg
    let expectedType := d.instantiateRevRange j i args
    unless (← compatibleTypes argType expectedType) do
      return none
    fType := b
  return fType

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
  if f.isAppOf ``lcCast then
    /-
    Given
    ```
    let _x.i := lcCast _ _ g
    let _x.j := _x.i a_1 ... a_n
    ```
    Try to eliminate cast when `g a_1 ... a_n` is also type correct
    -/
    guard <| f.getAppNumArgs == 3
    let g := f.appArg!
    let args := e.getAppArgs
    let some type ← checkApp? g args | failure
    guard (← compatibleTypes (← inferType e) type)
    return mkAppN g args
  else
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
  return mkAppN (.const declNameNew us) e.getAppArgs

/--
```
let _x : A := lcCast _ _ a
```
=> if `A` and type of `a` are equivalent
```
let _x : B := a
```
-/
def simpCast? (e : Expr) (expectedType : Expr) : OptionT SimpM Expr := do
  guard <| e.isAppOfArity ``lcCast 3
  let a := e.appArg!
  let type ← inferType a
  guard <| type.isErased || eqvTypes expectedType type
  return a

/-- Try to apply simple simplifications. -/
def simpValue? (e : Expr) (expectedType : Expr) : SimpM (Option Expr) :=
  -- TODO: more simplifications
  simpProj? e <|> simpAppApp? e <|> simpCtorDiscr? e <|> applyImplementedBy? e <|> simpCastCast? e <|> simpCast? e expectedType
