/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Util
import Lean.Meta.Tactic.Grind.AC.DenoteExpr
import Lean.Meta.Tactic.Grind.AC.Proof
public section
namespace Lean.Meta.Grind.AC
open Lean.Grind
/-- For each structure `s` s.t. `a` and `b` are elements of, execute `k` -/
@[specialize] def withExprs (a b : Expr) (k : ACM Unit) : GoalM Unit := do
  let ids₁ ← getTermOpIds a
  if ids₁.isEmpty then return ()
  let ids₂ ← getTermOpIds b
  go ids₁ ids₂
where
  go : List Nat → List Nat → GoalM Unit
    | [], _ => return ()
    | _, [] => return ()
    | id₁::ids₁, id₂::ids₂ => do
      if id₁ == id₂ then
        ACM.run id₁ k; go ids₁ ids₂
      else if id₁ < id₂ then
        go ids₁ (id₂::ids₂)
      else
        go (id₁::ids₁) ids₂

def asACExpr (e : Expr) : ACM AC.Expr := do
  if let some e' := (← getStruct).denote.find? { expr := e } then
    return e'
  else
    return .var ((← getStruct).varMap.find? { expr := e }).get!

def norm (e : AC.Expr) : ACM AC.Seq := do
  match (← isCommutative), (← hasNeutral) with
  | true,  true  => return e.toSeq.erase0.sort
  | true,  false => return e.toSeq.sort
  | false, true  => return e.toSeq.erase0
  | false, false => return e.toSeq

def saveDiseq (c : DiseqCnstr) : ACM Unit := do
  modifyStruct fun s => { s with diseqs := s.diseqs.push c }

def DiseqCnstr.eraseDup (c : DiseqCnstr) : ACM DiseqCnstr := do
  unless (← isIdempotent) do return c
  let lhs := c.lhs.eraseDup
  let rhs := c.rhs.eraseDup
  if c.lhs == lhs && c.rhs == rhs then
    return c
  else
    return { lhs, rhs, h := .erase_dup c }

def DiseqCnstr.assert (c : DiseqCnstr) : ACM Unit := do
  let c ← c.eraseDup
  -- TODO: simplify and check conflict
  trace[grind.ac.assert] "{← c.denoteExpr}"
  if c.lhs == c.rhs then
    c.setUnsat
  else
    saveDiseq c

@[export lean_process_ac_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := withExprs a b do
  trace[grind.ac.assert] "{a} = {b}"
  -- TODO

@[export lean_process_ac_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := withExprs a b do
  let ea ← asACExpr a
  let lhs ← norm ea
  let eb ← asACExpr b
  let rhs ← norm eb
  { lhs, rhs, h := .core a b ea eb : DiseqCnstr }.assert

end Lean.Meta.Grind.AC
