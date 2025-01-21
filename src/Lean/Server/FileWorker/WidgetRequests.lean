/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
prelude
import Lean.Widget.Basic
import Lean.Widget.InteractiveCode
import Lean.Widget.InteractiveGoal
import Lean.Widget.InteractiveDiagnostic

import Lean.Server.Rpc.RequestHandling
import Lean.Server.FileWorker.RequestHandling

/-! Registers all widget-related RPC procedures. -/

namespace Lean.Widget
open Server Lean.Elab

structure MsgToInteractive where
  msg : WithRpcRef MessageData
  indent : Nat
  deriving Inhabited, RpcEncodable

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
  deriving Inhabited, RpcEncodable

/-- Given elaborator info for a particular subexpression. Produce the `InfoPopup`.

The intended usage of this is for the infoview to pass the `InfoWithCtx` which
was stored for a particular `SubexprInfo` tag in a `TaggedText` generated with `ppExprTagged`.
 -/
def makePopup : WithRpcRef InfoWithCtx → RequestM (RequestTask InfoPopup)
  | ⟨i⟩ => RequestM.asTask do
    i.ctx.runMetaM i.info.lctx do
      let type? ← match (← i.info.type?) with
        | some type => some <$> ppExprTagged type
        | none => pure none
      let exprExplicit? ← match i.info with
        | Elab.Info.ofTermInfo ti
        | Elab.Info.ofDelabTermInfo { toTermInfo := ti, explicit := true, ..} =>
          some <$> ppExprTaggedWithoutTopLevelHighlight ti.expr (explicit := true)
        | Elab.Info.ofDelabTermInfo { toTermInfo := ti, explicit := false, ..} =>
          -- Keep the top-level tag so that users can also see the explicit version of the term on an additional hover.
          some <$> ppExprTagged ti.expr (explicit := false)
        | Elab.Info.ofFieldInfo fi => pure <| some <| TaggedText.text fi.fieldName.toString
        | _ => pure none
      return {
        type := type?
        exprExplicit := exprExplicit?
        doc := ← i.info.docString? : InfoPopup
      }
where
  ppExprTaggedWithoutTopLevelHighlight (e : Expr) (explicit : Bool) : MetaM CodeWithInfos := do
    let pp ← ppExprTagged e (explicit := explicit)
    return match pp with
      | .tag _ tt => tt
      | tt => tt

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.InteractiveDiagnostics.infoToInteractive
    (WithRpcRef InfoWithCtx)
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

structure GetGoToLocationParams where
  kind : GoToKind
  info : WithRpcRef InfoWithCtx
  deriving RpcEncodable

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getGoToLocation
    GetGoToLocationParams
    (Array Lsp.LocationLink)
    fun ⟨kind, ⟨i⟩⟩ => RequestM.asTask do
      let rc ← read
      let ls ← FileWorker.locationLinksOfInfo kind i
      if !ls.isEmpty then return ls
      -- TODO(WN): unify handling of delab'd (infoview) and elab'd (editor) applications
      let .ofTermInfo ti := i.info | return #[]
      let .app _ _ := ti.expr | return #[]
      let some nm := ti.expr.getAppFn.constName? | return #[]
      i.ctx.runMetaM ti.lctx <|
        locationLinksFromDecl rc.srcSearchPath rc.doc.meta.uri nm none

def lazyTraceChildrenToInteractive (children : WithRpcRef LazyTraceChildren) :
    RequestM (RequestTask (Array (TaggedText MsgEmbed))) :=
  RequestM.asTask do
    let ⟨indent, children⟩ := children
    children.mapM fun ⟨child⟩ =>
      msgToInteractive child (hasWidgets := true) (indent := indent)

builtin_initialize registerBuiltinRpcProcedure ``lazyTraceChildrenToInteractive _ _ lazyTraceChildrenToInteractive

end Lean.Widget
