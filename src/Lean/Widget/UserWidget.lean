/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers
-/
import Lean.Widget.Basic
import Lean.Data.Json
import Lean.Environment
import Lean.Server

open Lean

namespace Lean.Widget

/-- A custom piece of code that is run on the editor client.

The editor can use the `Lean.Widget.getWidgetSource` RPC method to
get this object.

See the [tutorial](doc/widgets.md) above this declaration for more information on
how to use the widgets system.

-/
structure WidgetSource where
  /-- Unique identifier for the widget. -/
  widgetSourceId : Name
  /-- Sourcetext of the code to run.-/
  sourcetext : String
  hash : String := toString <| hash sourcetext
  deriving Inhabited, ToJson, FromJson

namespace WidgetSource

builtin_initialize widgetSourceRegistry : MapDeclarationExtension WidgetSource ← mkMapDeclarationExtension `widgetSourceRegistry

private unsafe def attributeImplUnsafe : AttributeImpl where
  name := `widgetSource
  descr := "Mark a string as static code that can be loaded by a widget handler."
  applicationTime := AttributeApplicationTime.afterCompilation
  add decl _stx _kind := do
    let env ← getEnv
    let value ← evalConstCheck String ``String decl
    setEnv <| widgetSourceRegistry.insert env decl {widgetSourceId := decl, sourcetext := value}

@[implementedBy attributeImplUnsafe]
opaque attributeImpl : AttributeImpl

/-- Find the WidgetSource for given widget id. -/
protected def find? (env : Environment) (id : Name) : Option WidgetSource :=
  widgetSourceRegistry.find? env id

/-- Returns true if the environment contains the given widget id. -/
protected def contains (env : Environment) (id : Name) : Bool :=
  widgetSourceRegistry.contains env id

open Lean.Server in
/-- Gets the hash of the static javascript string for the given widget id, or throws if
there is no static javascript registered. -/
def getHash [Monad m] [MonadExcept RequestError m] (env : Environment) (id : Name) : m String := do
  let some j := WidgetSource.find? env id
    | throw <| RequestError.mk .invalidParams s!"getHash: No source found for {id}."
  return j.hash

builtin_initialize registerBuiltinAttribute attributeImpl

end WidgetSource

structure GetWidgetSourceParams where
  widgetSourceId : Name
  pos : Lean.Lsp.TextDocumentPositionParams
  deriving ToJson, FromJson

open Lean.Server Lean

open RequestM in
@[serverRpcMethod]
def getWidgetSource (args : GetWidgetSourceParams) : RequestM (RequestTask WidgetSource) :=
  RequestM.withWaitFindSnapAtPos args.pos fun snap => do
    let env := snap.cmdState.env
    if let some w := WidgetSource.find? env args.widgetSourceId then
      return w
    else
      throw <| RequestError.mk .invalidParams s!"No registered user-widget with id {args.widgetSourceId}"

open Lean Elab

/--
  Try to retrieve the `UserWidgetInfo` at a particular position.
-/
def widgetInfoAt? (text : FileMap) (t : InfoTree) (hoverPos : String.Pos) : List UserWidgetInfo :=
  t.deepestNodes fun
    | _ctx, i@(Info.ofUserWidgetInfo wi), _cs => do
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        let trailSize := i.stx.getTrailingSize
        -- show info at EOF even if strictly outside token + trail
        let atEOF := tailPos.byteIdx + trailSize == text.source.endPos.byteIdx
        guard <| pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + trailSize || atEOF)
        return wi
      else
        failure
    | _, _, _ => none

structure UserWidget where
  widgetSourceId : Name
  hash : String
  props : Json
  range? : Option Lsp.Range
  deriving ToJson, FromJson

structure GetWidgetsResponse where
  widgets : Array UserWidget
  deriving ToJson, FromJson

open RequestM in
/-- Get the `UserWidget`s present at a particular position. -/
@[serverRpcMethod]
def getWidgets (args : Lean.Lsp.TextDocumentPositionParams) : RequestM (RequestTask (GetWidgetsResponse)) := do
  let doc ← readDoc
  let filemap := doc.meta.text
  let pos := filemap.lspPosToUtf8Pos args.position
  withWaitFindSnapAtPos args fun snap => do
      let env := snap.env
      let ws := widgetInfoAt? filemap snap.infoTree pos
      let ws ← ws.toArray.mapM (fun w => do
        let hash ← WidgetSource.getHash env w.widgetSourceId
        return {
          widgetSourceId := w.widgetSourceId,
          hash := hash,
          props := w.props,
          range? := String.Range.toLspRange filemap <$> Syntax.getRange? w.stx,
        })
      return {widgets := ws}

/-- Save a user-widget instance to the infotree. -/
def saveWidgetInfo [Monad m] [MonadEnv m] [MonadError m] [MonadInfoTree m] (widgetSourceId : Name) (props : Json) (stx : Syntax):  m Unit := do
  let info := Info.ofUserWidgetInfo {
    widgetSourceId := widgetSourceId,
    props := props,
    stx := stx,
  }
  pushInfoLeaf info

/-!  # Widget command -/

syntax (name := widgetCmd) "#widget " ident term : command

private unsafe def  evalJsonUnsafe (stx : Syntax) : TermElabM Json := do
  let e ← Term.elabTerm stx (mkConst ``Json)
  let e ← Meta.instantiateMVars e
  Term.evalExpr Json ``Json e

@[implementedBy evalJsonUnsafe]
private opaque evalJson (stx : Syntax) : TermElabM Json

open Elab Command in
/-- Use this to place a widget. Useful for debugging widgets. -/
@[commandElab widgetCmd] def elabWidgetCmd : CommandElab := fun
  | stx@`(#widget $id:ident $props) => do
    let props : Json ← runTermElabM none (fun _ => evalJson props)
    saveWidgetInfo id.getId props stx
    return ()
  | _ => throwUnsupportedSyntax

end Lean.Widget
