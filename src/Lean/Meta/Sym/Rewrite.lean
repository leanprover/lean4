/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SimpM
public import Lean.Meta.Sym.SimpFun
namespace Lean.Meta.Sym.Simp

public def rewrite : SimpFun := fun e => do
  -- **TODO**
  return { expr := e }

end Lean.Meta.Sym.Simp
