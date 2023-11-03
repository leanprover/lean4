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

-/
def preprocess (e : Expr) : CoreM Expr :=
  Core.transform e
    (post := fun e =>
      if e.isApp && e.getAppFn.isMData && e.getAppFn.mdata!.isRecApp then
        return .visit (e.withApp fun f as => .mdata f.mdata! (mkAppN (f.mdataExpr!) as))
      else
        return .continue)

end Lean.Elab.WF
