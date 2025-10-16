/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.RecAppSyntax
public import Lean.Meta.WHNF

public section

namespace Lean.Elab.Structural
open Meta

private def shouldBetaReduce (e : Expr) (recFnNames : Array Name) : Bool :=
  if e.isHeadBetaTarget then
    e.getAppFn.find? (fun e => e.isConst && recFnNames.contains e.constName!) |>.isSome
  else
    false

/--
Preprocesses the expressions to improve the effectiveness of `elimRecursion`.

* Beta reduce terms where the recursive function occurs in the lambda term.
  Example:
  ```
  def f : Nat → Nat
    | 0 => 1
    | i+1 => (fun x => f x) i
  ```

* Floats out the RecApp markers.
  Example:
  ```
  def f : Nat → Nat
    | 0 => 1
    | i+1 => (f x) i
  ```

* Unfold auxiliary definitions abstracting over the function call
  (typically abstracted) proofs.

-/
def preprocess (e : Expr) (recFnNames : Array Name) (numFixedParams : Nat) : CoreM Expr := do
  let e ← unfoldIfArgIsAppOf recFnNames numFixedParams e
  Core.transform e
    (pre := fun e =>
      if shouldBetaReduce e recFnNames then
        return .visit e.headBeta
      else
        return .continue)
    (post := fun e => do
      if e.isApp && e.getAppFn.isMData then
        let .mdata m f := e.getAppFn | unreachable!
        if m.isRecApp then
          return .done (.mdata m (f.beta e.getAppArgs))
      return .continue)


end Lean.Elab.Structural
