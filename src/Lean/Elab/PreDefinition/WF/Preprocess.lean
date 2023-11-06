/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Elab.RecAppSyntax

namespace Lean.Elab.WF
open Meta

/--
Preprocesses the expessions to improve the effectiveness of `wfRecursion`.

* Floats out the RecApp markers.
  Example:
  ```
  def f : Nat → Nat
    | 0 => 1
    | i+1 => (f x) i
  ```

Unlike `Lean.Elab.Structural.preprocess`, do _not_ beta-reduce, as it could
remove `let_fun`-lambdas that contain explicit termination proofs.
-/
def preprocess (e : Expr) : CoreM Expr :=
  Core.transform e
    (post := fun e =>
      match e with
      | .app (.mdata m f) a =>
        if m.isRecApp then
          return .done (.mdata m (.app f a))
        else
          return .done e
      | _ => return .done e)

end Lean.Elab.WF
