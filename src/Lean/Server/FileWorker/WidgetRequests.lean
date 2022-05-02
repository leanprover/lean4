/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Widget.Basic
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
  registerBuiltinRpcProcedure
    `Lean.Widget.InteractiveDiagnostics.msgToInteractive
    MsgToInteractive
    (TaggedText MsgEmbed)
    fun ⟨⟨m⟩, i⟩ => RequestM.asTask do msgToInteractive m i (hasWidgets := true)

structure InfoPopup where
  type : Option CodeWithInfos
  exprExplicit : Option CodeWithInfos
  doc : Option String
  deriving Inhabited, RpcEncoding

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.InteractiveDiagnostics.infoToInteractive
    (WithRpcRef InfoWithCtx)
    InfoPopup
    fun ⟨i⟩ => RequestM.asTask do
      i.ctx.runMetaM i.info.lctx do
        let type? ← match (← i.info.type?) with
          | some type => some <$> exprToInteractive type
          | none => pure none
        let exprExplicit? ← match i.info with
          | Elab.Info.ofTermInfo ti =>
            let ti ← exprToInteractive ti.expr (explicit := true)
            -- remove top-level expression highlight
            pure <| some <| match ti with
              | .tag _ tt => tt
              | tt => tt
          | Elab.Info.ofFieldInfo fi => pure <| some <| TaggedText.text fi.fieldName.toString
          | _ => pure none
        return {
          type := type?
          exprExplicit := exprExplicit?
          doc := ← i.info.docString? : InfoPopup
        }

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getInteractiveGoals
    Lsp.PlainGoalParams
    (Option InteractiveGoals)
    FileWorker.getInteractiveGoals

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getInteractiveTermGoal
    Lsp.PlainTermGoalParams
    (Option InteractiveTermGoal)
    FileWorker.getInteractiveTermGoal

structure GetInteractiveDiagnosticsParams where
  /-- Return diagnostics for these lines only if present,
  otherwise return all diagnostics. -/
  lineRange? : Option Lsp.LineRange
  deriving Inhabited, FromJson, ToJson

open RequestM in
def getInteractiveDiagnostics (params : GetInteractiveDiagnosticsParams) : RequestM (RequestTask (Array InteractiveDiagnostic)) := do
  let doc ← readDoc
  let rangeEnd := params.lineRange?.map fun range =>
    doc.meta.text.lspPosToUtf8Pos ⟨range.«end», 0⟩
  let t ← doc.cmdSnaps.waitAll fun snap => rangeEnd.all (snap.beginPos < ·)
  pure <| t.map fun (snaps, _) =>
    let diags? := snaps.getLast?.map fun snap =>
      snap.interactiveDiags.toArray.filter fun diag =>
        params.lineRange?.all fun ⟨s, e⟩ =>
          -- does [s,e) intersect [diag.fullRange.start.line,diag.fullRange.end.line)?
          s ≤ diag.fullRange.start.line ∧ diag.fullRange.start.line < e ∨
          diag.fullRange.start.line ≤ s ∧ s < diag.fullRange.end.line
    pure <| diags?.getD #[]

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getInteractiveDiagnostics
    GetInteractiveDiagnosticsParams
    (Array InteractiveDiagnostic)
    getInteractiveDiagnostics

end Lean.Widget
