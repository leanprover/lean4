/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform

namespace Lean.Elab.Structural
open Meta

private def shouldBetaReduce (e : Expr) (recFnName : Name) : Bool :=
  if e.isHeadBetaTarget then
    e.getAppFn.find? (·.isConstOf recFnName) |>.isSome
  else
    false

/--
  Beta reduce terms where the recursive function occurs in the lambda term.
  This is useful to improve the effectiveness of `elimRecursion`.
  Example:
  ```
  def f : Nat → Nat
    | 0 => 1
    | i+1 => (fun x => f x) i
  ```
-/
def preprocess (e : Expr) (recFnName : Name) : CoreM Expr :=
  Core.transform e
   fun e =>
     if shouldBetaReduce e recFnName then
       return .visit e.headBeta
     else
       return .continue

end Lean.Elab.Structural
