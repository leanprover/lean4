/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
namespace Lean.Meta.Sym.DSimp

public def Result.markAsDone : Result → Result
  | .rfl _    => .rfl true
  | .step e _ => .step e true

public def Result.getResultExpr : Expr → Result → Expr
  | e, .rfl _    => e
  | _, .step e _ => e

end Lean.Meta.Sym.DSimp
