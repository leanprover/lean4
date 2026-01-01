/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SimpM
namespace Lean.Meta.Sym.Simp

@[export lean_sym_simp]
def simpImpl (e : Expr) : SimpM Result := do
  throwError "NIY {e}"

end Lean.Meta.Sym.Simp
