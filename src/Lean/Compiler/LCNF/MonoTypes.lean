/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

/--
Convert a LCNF type from the base phase to the mono phase.

LCNF types in the mono phase do not have dependencies,
and universe levels have been erased.

The type contains only `→` and constants.
-/
partial def toMonoType (type : Expr) : CompilerM Expr := do
  let type := type.headBeta
  if type.isAnyType then
    return anyTypeExpr
  else if type.isErased then
    return erasedExpr
  else if isTypeFormerType type then
    return erasedExpr
  else match type with
    | .const ..        => visitApp type #[]
    | .app ..          => type.withApp visitApp
    | .forallE _ d b _ => mkArrow (← toMonoType d) (← toMonoType (b.instantiate1 anyTypeExpr))
    | _                => return anyTypeExpr
where
  visitApp (f : Expr) (args : Array Expr) : CompilerM Expr := do
    match f with
    | .const declName _ =>
      let mut result := mkConst declName
      for arg in args do
        let arg := arg.headBeta
        if arg.isAnyType || arg.isErased then
          result := mkApp result arg
        else
          let argType := (← inferType arg).headBeta
          if argType.isAnyType || argType matches .sort _ then
            result := mkApp result (← toMonoType arg)
          else
            result := mkApp result erasedExpr
      return result
    | _ => return anyTypeExpr

end Lean.Compiler.LCNF