/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.HeadIndex
import Lean.Meta.Basic

namespace Lean.Meta

/--
  A mapping that indentifies definitionally equal expressions.
  We implement it as a mapping from `HeadIndex` to `Std.AssocList Expr α`.

  Remark: this map may be quite inefficient if there are many `HeadIndex` collisions.
-/
structure KExprMap (α : Type) where
  map : Std.PHashMap HeadIndex (Std.AssocList Expr α) := {}
  deriving Inhabited

/-- Return `some v` if there is an entry `e ↦ v` in `m`. -/
def KExprMap.find? (m : KExprMap α) (e : Expr) : MetaM (Option α) := do
  match m.map.find? e.toHeadIndex with
  | none => return none
  | some ps =>
    for ⟨e', a⟩ in ps do
      if (← isDefEq e e') then
        return some a
    return none

private def updateList (ps : Std.AssocList Expr α) (e : Expr) (v : α) : MetaM (Std.AssocList Expr α) := do
  match ps with
  | Std.AssocList.nil => return Std.AssocList.cons e v ps
  | Std.AssocList.cons e' v' ps =>
    if (← isDefEq e e') then
      return Std.AssocList.cons e v ps
    else
      return Std.AssocList.cons e' v' (← updateList ps e v)

/-- Insert `e ↦ v` into `m` -/
def KExprMap.insert (m : KExprMap α) (e : Expr) (v : α) : MetaM (KExprMap α) :=
  let k := e.toHeadIndex
  match m.map.find? k with
  | none    => return { map := m.map.insert k (Std.AssocList.cons e v Std.AssocList.nil) }
  | some ps => return { map := m.map.insert k (← updateList ps e v) }

end Lean.Meta
