/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SimpM
namespace Lean.Meta.Sym.Simp

public def Result.getProof (result : Result) : SymM Expr := do
  let some proof := result.proof? | mkEqRefl result.expr
  return proof

end Lean.Meta.Sym.Simp
