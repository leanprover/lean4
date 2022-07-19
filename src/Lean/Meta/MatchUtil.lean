/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Recognizers
import Lean.Meta.Basic

namespace Lean.Meta

@[inline] def testHelper (e : Expr) (p : Expr → MetaM Bool) : MetaM Bool := do
  if (← p e) then
    return true
  else
    p (← whnf e)

@[inline] def matchHelper? (e : Expr) (p? : Expr → MetaM (Option α)) : MetaM (Option α) := do
  match (← p? e) with
  | none => p? (← whnf e)
  | s    => return s

/-- Matches `e` with `lhs = (rhs : α)` and returns `(α, lhs, rhs)`. -/
def matchEq? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
  matchHelper? e fun e => return Expr.eq? e

def matchHEq? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) :=
  matchHelper? e fun e => return Expr.heq? e

/--
  Return `some (α, lhs, rhs)` if `e` is of the form `@Eq α lhs rhs` or `@HEq α lhs α rhs`
-/
def matchEqHEq? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if let some r ← matchEq? e then
    return some r
  else if let some (α, lhs, β, rhs) ← matchHEq? e then
    if (← isDefEq α β) then
      return some (α, lhs, rhs)
    return none
  else
    return none

def matchFalse (e : Expr) : MetaM Bool := do
  testHelper e fun e => return e.isConstOf ``False

def matchNot? (e : Expr) : MetaM (Option Expr) :=
  matchHelper? e fun e => do
    if let some e := e.not? then
      return e
    else if let some (a, b) := e.arrow? then
      if (← matchFalse b) then return some a else return none
    else
      return none

def matchNe? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
  matchHelper? e fun e => do
    if let some r := e.ne? then
      return r
    else if let some e ← matchNot? e then
      matchEq? e
    else
      return none

def matchConstructorApp? (e : Expr) : MetaM (Option ConstructorVal) := do
  let env ← getEnv
  matchHelper? e fun e =>
    return e.isConstructorApp? env

end Lean.Meta
