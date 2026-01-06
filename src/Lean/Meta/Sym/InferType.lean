/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
namespace Lean.Meta.Sym

def inferTypeWithoutCache (e : Expr) : MetaM Expr :=
  withReader (fun c => { c with cacheInferType := false }) do
    Meta.inferType e

def getLevelWithoutCache (type : Expr) : MetaM Level :=
  withReader (fun c => { c with cacheInferType := false }) do
    Meta.getLevel type

/-- Returns the type of `e`. -/
public def inferType (e : Expr) : SymM Expr := do
  if let some type := (← get).inferType.find? { expr := e } then
    return type
  else
    let type ← shareCommonInc (← inferTypeWithoutCache e)
    modify fun s => { s with inferType := s.inferType.insert { expr := e } type }
    return type

@[inherit_doc Meta.getLevel]
public def getLevel (type : Expr) : SymM Level := do
  if let some u := (← get).getLevel.find? { expr := type } then
    return u
  else
    let u ← getLevelWithoutCache type
    modify fun s => { s with getLevel := s.getLevel.insert { expr := type } u }
    return u

public def mkEqRefl (e : Expr) : SymM Expr := do
  let α ← inferType e
  let u ← getLevel α
  return mkApp2 (mkConst ``Eq.refl [u]) α e

end Lean.Meta.Sym
