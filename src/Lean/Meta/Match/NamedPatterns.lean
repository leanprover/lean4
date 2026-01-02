/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.Transform
import Lean.Meta.WHNF
/-!
Helper functions around named patterns
-/
namespace Lean.Meta.Match

public def mkNamedPattern (x h p : Expr) : MetaM Expr :=
  mkAppM ``namedPattern #[x, p, h]

public def isNamedPattern (e : Expr) : Bool :=
  let e := e.consumeMData
  e.getAppNumArgs == 4 && e.getAppFn.consumeMData.isConstOf ``namedPattern

public def isNamedPattern? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.getAppNumArgs == 4 && e.getAppFn.consumeMData.isConstOf ``namedPattern then
    some e
  else
    none

public def unfoldNamedPattern (e : Expr) : MetaM Expr := do
  let visit (e : Expr) : MetaM TransformStep := do
    if let some e := isNamedPattern? e then
      if let some eNew ← unfoldDefinition? e then
        return TransformStep.visit eNew
    return .continue
  Meta.transform e (pre := visit)

end Lean.Meta.Match
