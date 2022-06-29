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
  id       : Name   -- id of the theorem at `SimpTheorems`
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
  let hs ← withMVarContext (← get).mvarId do getPropHyps
  let hsNonDeps ← getNondepPropHyps (← get).mvarId
  let mut simpThms := (← get).ctx.simpTheorems
  for h in hs do
    let localDecl ← getLocalDecl h
    unless simpThms.isErased localDecl.userName do
      let fvarId := localDecl.fvarId
      let proof  := localDecl.toExpr
      let id     ← mkFreshUserName `h
      simpThms ← simpThms.addTheorem proof (name? := id)
      modify fun s => { s with ctx.simpTheorems := simpThms }
      if hsNonDeps.contains h then
        -- We only simplify nondependent hypotheses
        let entry : Entry := { fvarId := fvarId, userName := localDecl.userName, id := id, type := (← instantiateMVars localDecl.type), proof := proof }
        modify fun s => { s with entries := s.entries.push entry }

private abbrev getSimpTheorems : M SimpTheoremsArray :=
  return (← get).ctx.simpTheorems

private partial def loop : M Bool := do
  modify fun s => { s with modified := false }
  -- simplify entries
  for i in [:(← get).entries.size] do
    let entry := (← get).entries[i]
    let ctx := (← get).ctx
    -- We disable the current entry to prevent it to be simplified to `True`
    let simpThmsWithoutEntry := (← getSimpTheorems).eraseTheorem entry.id
    let ctx := { ctx with simpTheorems := simpThmsWithoutEntry }
    match (← simpStep (← get).mvarId entry.proof entry.type ctx) with
    | none => return true -- closed the goal
    | some (proofNew, typeNew) =>
      unless typeNew == entry.type do
        /- The theorem for the simplified entry must use the same `id` of the theorem before simplification. Otherwise,
           the previous versions can be used to self-simplify the new version. For example, suppose we have
           ```
            x : Nat
            h : x ≠ 0
            ⊢ Unit
           ```
           In the first round, `h : x ≠ 0` is simplified to `h : ¬ x = 0`. If we don't use the same `id`, in the next round
           the first version would simplify it to `h : True`.

           We must use `mkExpectedTypeHint` because `inferType proofNew` may not be equal to `typeNew` when
           we have theorems marked with `rfl`.
        -/
        let simpThmsNew ← (← getSimpTheorems).addTheorem (← mkExpectedTypeHint proofNew typeNew) (name? := entry.id)
        modify fun s => { s with
          modified         := true
          ctx.simpTheorems := simpThmsNew
          entries[i]       := { entry with type := typeNew, proof := proofNew, id := entry.id }
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
