/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.Have
import Lean.Meta.Sym.Simp.Forall
namespace Lean.Meta.Sym.Simp
/--
Simplify telescope binders (`have`-expression values, and arrow hypotheses)
but not the final body. This simproc is useful to simplify target before
introducing.
-/
public partial def simpTelescope : Simproc := fun e => do
  match e with
  | .letE .. =>
    simpLet' (simpLambda' simpTelescope) e
  | .forallE .. =>
    simpForall' (simpArrow := simpArrowTelescope simpTelescope) (simpBody := simpLambda' simpTelescope) e
  | _ => return .rfl

end Lean.Meta.Sym.Simp
