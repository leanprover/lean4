/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.CollectFVars
import Lean.Util.FindExpr

namespace Lean.Expr

/-- Returns true if the free variables in `a` are subset of the free variables in `b`. -/
def fvarsSubset (a b : Expr) : Bool :=
  if !a.hasFVar then
    true -- Empty set is subset of anything
  else if !b.hasFVar then
    false -- Empty set is not a superset of a nonempty set.
  else
    let s := collectFVars {} b
    Option.isNone <| a.findExt? fun e =>
      if !e.hasFVar then .done
      else if e.isFVar && !s.fvarSet.contains e.fvarId! then .found
      else .visit

end Lean.Expr
