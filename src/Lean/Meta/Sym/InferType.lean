/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
namespace Lean.Meta.Sym

/-- Returns the type of `e`. -/
def inferType (e : Expr) : SymM Expr := do
  if let some type := (← get).inferType.find? { expr := e } then
    return type
  else
    let type ← Meta.inferType e
    modify fun s => { s with inferType := s.inferType.insert { expr := e } type }
    return type

end Lean.Meta.Sym
