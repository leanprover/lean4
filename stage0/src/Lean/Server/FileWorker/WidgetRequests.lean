/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Widget.InteractiveCode
import Lean.Widget.InteractiveGoal
import Lean.Widget.InteractiveDiagnostic

import Lean.Server.Rpc.RequestHandling
import Lean.Server.FileWorker.RequestHandling

/-! Registers all widget-related RPC procedures. -/

namespace Lean.Widget
open Server

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

builtin_initialize
  registerRpcCallHandler
    `Lean.Widget.getInteractiveGoals
    Lsp.PlainGoalParams
    (Option InteractiveGoals)
    FileWorker.getInteractiveGoals

  registerRpcCallHandler
    `Lean.Widget.getInteractiveTermGoal
    Lsp.PlainTermGoalParams
    (Option InteractiveTermGoal)
    FileWorker.getInteractiveTermGoal

open RequestM in
def getInteractiveDiagnostics (_ : Json) : RequestM (RequestTask (Array InteractiveDiagnostic)) := do
  let doc ← readDoc
  let t₁ ← doc.cmdSnaps.waitAll
  t₁.map fun (snaps, _) => snaps.getLast!.interactiveDiags.toArray

builtin_initialize
  registerRpcCallHandler
    `Lean.Widget.getInteractiveDiagnostics
    Json
    (Array InteractiveDiagnostic)
    getInteractiveDiagnostics

end Lean.Widget
