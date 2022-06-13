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

/-- Parameters for the `Lean.Widget.ppExprTagged` RPC.-/
structure PPExprTaggedParams where
  expr : WithRpcRef ExprWithCtx
  explicit : Bool
  deriving Inhabited, RpcEncoding

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.ppExprTagged
    PPExprTaggedParams
    CodeWithInfos
    fun ⟨⟨ctx, lctx, expr⟩, explicit⟩ => RequestM.asTask do
      ctx.runMetaM lctx do
        ppExprTagged expr explicit

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

/-- The information that the infoview uses to render a popup
for when the user hovers over an expression.
-/
structure InfoPopup where
  type : Option CodeWithInfos
  /-- Show the term with the implicit arguments. -/
  exprExplicit : Option CodeWithInfos
  /-- Docstring. In markdown. -/
  doc : Option String
  deriving Inhabited, RpcEncoding

/-- Given elaborator info for a particular subexpression. Produce the `InfoPopup`.

The intended usage of this is for the infoview to pass the `ExprWithCtx` which
was stored for a particular `SubexprInfo` tag in a `TaggedText` generated with `ppExprTagged`.
 -/
def makePopup : WithRpcRef ExprWithCtx → RequestM (RequestTask InfoPopup)
    | ⟨i⟩ => RequestM.asTask do
      i.ctx.runMetaM i.lctx do
        let type? ←
          (do return some <|← ppExprTagged <|← Meta.inferType i.expr)
          <|> pure none
        let ti ← ppExprTagged i.expr (explicit := true)
        -- remove top-level expression highlight
        let tt := match ti with
          | .tag _ tt => tt
          | tt => tt
        let doc? ←
          if let some n := i.expr.constName?
          then findDocString? (← getEnv) n else pure none
        return {
          type := type?
          exprExplicit := some tt
          doc := doc? : InfoPopup
        }

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.InteractiveDiagnostics.infoToInteractive
    (WithRpcRef ExprWithCtx)
    InfoPopup
    makePopup

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

structure GetGoToLocationParams where
  kind : GoToKind
  info : WithRpcRef ExprWithCtx
  deriving RpcEncoding

def getGoToLocation : GetGoToLocationParams → RequestM (RequestTask (Array Lsp.LocationLink))
  | ⟨kind, ⟨i⟩⟩ => RequestM.asTask do
    let rc ← read
    let ls ← FileWorker.locationLinksOfInfo kind i.ctx (ExprWithCtx.toTermInfo i)
    if !ls.isEmpty then return ls
    -- TODO(WN): unify handling of delab'd (infoview) and elab'd (editor) applications
    let .app _ _ _ := i.expr | return #[]
    let some nm := i.expr.getAppFn.constName? | return #[]
    i.ctx.runMetaM i.lctx <|
      locationLinksFromDecl rc.srcSearchPath rc.doc.meta.uri nm none

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getGoToLocation
    GetGoToLocationParams
    (Array Lsp.LocationLink)
    getGoToLocation

end Lean.Widget
