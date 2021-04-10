/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Simp.Main

namespace Lean.Meta

namespace SimpAll

structure Entry where
  fvarId   : FVarId -- original fvarId
  userName : Name
  id       : Name   -- id of the lemma at `SimpLemmas`
  type     : Expr
  proof    : Expr
  deriving Inhabited

structure State where
  modified : Bool := false
  mvarId   : MVarId
  entries  : Array Entry := #[]
  ctx      : Simp.Context

abbrev M := StateRefT State MetaM

private def initEntries : M Unit := do
  let hs ← getNondepPropHyps (← get).mvarId
  let erased := (← get).ctx.simpLemmas.erased
  for h in hs do
    let localDecl ← getLocalDecl h
    unless erased.contains localDecl.userName do
      let fvarId := localDecl.fvarId
      let proof  := localDecl.toExpr
      let id     ← mkFreshUserName `h
      let simpLemmas ← (← get).ctx.simpLemmas.add #[] proof (name? := id)
      let entry : Entry := { fvarId := fvarId, userName := localDecl.userName, id := id, type := (← instantiateMVars localDecl.type), proof := proof }
      modify fun s => { s with entries := s.entries.push entry, ctx.simpLemmas := simpLemmas }

private abbrev getSimpLemmas : M SimpLemmas :=
  return (← get).ctx.simpLemmas

private partial def loop : M Bool := do
  modify fun s => { s with modified := false }
  -- simplify entries
  for i in [:(← get).entries.size] do
    let entry := (← get).entries[i]
    let ctx := (← get).ctx
    -- We disable the current entry to prevent it to be simplified to `True`
    let simpLemmasWithoutEntry ← (← getSimpLemmas).eraseCore entry.id
    let ctx := { ctx with simpLemmas := simpLemmasWithoutEntry }
    match (← simpStep (← get).mvarId entry.proof entry.type ctx) with
    | none => return true -- closed the goal
    | some (proofNew, typeNew) =>
      unless typeNew == entry.type do
        let id ← mkFreshUserName `h
        let simpLemmasNew ← (← getSimpLemmas).add #[] proofNew (name? := id)
        modify fun s => { s with
          modified       := true
          ctx.simpLemmas := simpLemmasNew
          entries[i]     := { entry with type := typeNew, proof := proofNew, id := id }
        }
  -- simplify target
  let mvarId := (← get).mvarId
  match (← simpTarget mvarId (← get).ctx) with
  | none => return true
  | some mvarIdNew =>
    unless mvarId == mvarIdNew do
      modify fun s => { s with
        modified := true
        mvarId   := mvarIdNew
      }
  if (← get).modified then
    loop
  else
    return false

def main : M (Option MVarId) := do
  initEntries
  if (← loop) then
    return none -- close the goal
  else
    let mvarId := (← get).mvarId
    let entries := (← get).entries
    let (_, mvarId) ← assertHypotheses mvarId (entries.map fun e => { userName := e.userName, type := e.type, value := e.proof })
    tryClearMany mvarId (entries.map fun e => e.fvarId)

end SimpAll

def simpAll (mvarId : MVarId) (ctx : Simp.Context) : MetaM (Option MVarId) := do
  withMVarContext mvarId do
    SimpAll.main.run' { mvarId := mvarId, ctx := ctx }

end Lean.Meta
