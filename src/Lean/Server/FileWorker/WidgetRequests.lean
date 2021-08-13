/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Widget.InteractiveCode
import Lean.Widget.InteractiveGoal
import Lean.Widget.InteractiveDiagnostic

import Lean.Server.Rpc.RequestHandling

/-! Registers all widget-related RPC procedures. -/

namespace Lean.Widget
open Server

builtin_initialize
  registerRpcCallHandler
    `Lean.Widget.ExprWithCtx.tagged
    (WithRpcRef ExprWithCtx)
     CodeWithInfos
    fun ⟨e⟩ => RequestM.asTask do e.ctx.runMetaM e.lctx (exprToInteractive e.expr)

  registerRpcCallHandler
    `Lean.Widget.ExprWithCtx.taggedExplicit
    (WithRpcRef ExprWithCtx)
    CodeWithInfos
    fun ⟨e⟩ => RequestM.asTask do e.ctx.runMetaM e.lctx (exprToInteractiveExplicit e.expr)

  registerRpcCallHandler
    `Lean.Widget.ExprWithCtx.inferType
    (WithRpcRef ExprWithCtx)
    (WithRpcRef ExprWithCtx)
    fun ⟨e⟩ => RequestM.asTask do WithRpcRef.mk <$> e.ctx.runMetaM e.lctx (inferType e.expr)

structure MsgToInteractive where
  msg : WithRpcRef MessageData
  indent : Nat
  deriving Inhabited, RpcEncoding

builtin_initialize
  registerRpcCallHandler
    `Lean.Widget.InteractiveDiagnostics.msgToInteractive
    MsgToInteractive
    (TaggedText MsgEmbed)
    fun ⟨⟨m⟩, i⟩ => RequestM.asTask do msgToInteractive m i

structure InfoPopup where
  type : Option CodeWithInfos
  exprExplicit : Option CodeWithInfos
  doc : Option String
  deriving Inhabited, RpcEncoding

builtin_initialize
  registerRpcCallHandler
    `Lean.Widget.InteractiveDiagnostics.infoToInteractive
    (WithRpcRef InfoWithCtx)
    InfoPopup
    fun ⟨i⟩ => RequestM.asTask do
      i.ctx.runMetaM i.lctx do
        let type? ← match (← i.info.type?) with
          | some type => some <$> exprToInteractive type
          | none => none
        let exprExplicit? ← match i.info with
          | Elab.Info.ofTermInfo ti => some <$> exprToInteractiveExplicit ti.expr
          | Elab.Info.ofFieldInfo fi => some (TaggedText.text fi.fieldName.toString)
          | _ => none
        return {
          type := type?
          exprExplicit := exprExplicit?
          doc := ← i.info.docString? : InfoPopup
        }

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask InteractiveGoals) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- NOTE: use `>=` since the cursor can be *after* the input
  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := return { goals := #[] }) fun snap => do
      for t in snap.cmdState.infoState.trees do
        if let rs@(_ :: _) := t.goalsAt? doc.meta.text hoverPos then
          let goals ← List.join <$> rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter } =>
            let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
            let goals := if useAfter then ti.goalsAfter else ti.goalsBefore
            ci.runMetaM {} <| goals.mapM (fun g => Meta.withPPInaccessibleNames (goalToInteractive g))
          return { goals := goals.toArray }

      return { goals := #[] }

open RequestM in
partial def getInteractiveTermGoal (p : Lsp.PlainTermGoalParams)
    : RequestM (RequestTask (Option InteractiveGoal)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure none) fun snap => do
      for t in snap.cmdState.infoState.trees do
        if let some (ci, i@(Elab.Info.ofTermInfo ti)) := t.termGoalAt? hoverPos then
         let ty ← ci.runMetaM i.lctx do
           Meta.instantiateMVars <| ti.expectedType?.getD (← Meta.inferType ti.expr)
         -- for binders, hide the last hypothesis (the binder itself)
         let lctx' := if ti.isBinder then i.lctx.pop else i.lctx
         let goal ← ci.runMetaM lctx' do
           Meta.withPPInaccessibleNames <| goalToInteractive (← Meta.mkFreshExprMVar ty).mvarId!
         --let range := if let some r := i.range? then r.toLspRange text else ⟨p.position, p.position⟩
         return some goal
      return none

builtin_initialize
  registerRpcCallHandler
    `Lean.Widget.getInteractiveGoals
    Lsp.PlainGoalParams
    InteractiveGoals
    getInteractiveGoals

  registerRpcCallHandler
    `Lean.Widget.getInteractiveTermGoal
    Lsp.PlainTermGoalParams
    (Option InteractiveGoal)
    getInteractiveTermGoal

end Lean.Widget
