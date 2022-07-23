/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers
-/
import Lean.Widget.Basic
import Lean.Data.Json
import Lean.Environment
import Lean.Server
import Lean.Elab.Eval

open Lean

namespace Lean.Widget

/-- A custom piece of code that is run on the editor client.

The editor can use the `Lean.Widget.getWidgetSource` RPC method to
get this object.

See the [manual entry](doc/widgets.md) above this declaration for more information on
how to use the widgets system.

-/
structure WidgetSource where
  /-- Sourcetext of the code to run.-/
  sourcetext : String
  deriving Inhabited, ToJson, FromJson

/-- Use this structure and the `@[widget]` attribute to define your own widgets.

```lean
@[widget]
def rubiks : UserWidgetDefinition :=
  { name := "Rubiks cube app"
    javascript := include_str ...
  }
```
-/
structure UserWidgetDefinition where
  /-- Pretty name of user widget to display to the user. -/
  name : String
  /-- An ESmodule that exports a react component to render. -/
  javascript: String
  deriving Inhabited, ToJson, FromJson

structure UserWidget where
  id : Name
  /-- Pretty name of widget to display to the user.-/
  name : String
  javascriptHash: UInt64
  deriving Inhabited, ToJson, FromJson

private abbrev WidgetSourceRegistry := SimplePersistentEnvExtension
    (UInt64 × Name)
    (Std.RBMap UInt64 Name compare)

-- Mapping widgetSourceId to hash of sourcetext
builtin_initialize userWidgetRegistry : MapDeclarationExtension UserWidget ← mkMapDeclarationExtension `widgetRegistry
builtin_initialize widgetSourceRegistry : WidgetSourceRegistry ←
  registerSimplePersistentEnvExtension {
    name          := `widgetSourceRegistry
    addImportedFn := fun xss => xss.foldl (Array.foldl (fun s n => s.insert n.1 n.2)) ∅
    addEntryFn    := fun s n => s.insert n.1 n.2
    toArrayFn     := fun es => es.toArray
  }

private unsafe def getUserWidgetDefinitionUnsafe
  (decl : Name) : CoreM UserWidgetDefinition :=
  evalConstCheck UserWidgetDefinition ``UserWidgetDefinition decl

@[implementedBy getUserWidgetDefinitionUnsafe]
private opaque getUserWidgetDefinition
  (decl : Name) : CoreM UserWidgetDefinition

private def attributeImpl : AttributeImpl where
  name := `widget
  descr := "Mark a string as static code that can be loaded by a widget handler."
  applicationTime := AttributeApplicationTime.afterCompilation
  add decl _stx _kind := do
    let env ← getEnv
    let defn ← getUserWidgetDefinition decl
    let javascriptHash := hash defn.javascript
    let env := userWidgetRegistry.insert env decl {id := decl, name := defn.name, javascriptHash}
    let env := widgetSourceRegistry.addEntry env (javascriptHash, decl)
    setEnv <| env

builtin_initialize registerBuiltinAttribute attributeImpl

/-- Input for `getWidgetSource` RPC. -/
structure GetWidgetSourceParams where
  /-- The hash of the sourcetext to retrieve. -/
  hash: UInt64
  pos : Lean.Lsp.Position
  deriving ToJson, FromJson

open Lean.Server Lean RequestM in
@[serverRpcMethod]
def getWidgetSource (args : GetWidgetSourceParams) : RequestM (RequestTask WidgetSource) :=
  RequestM.withWaitFindSnapAtPos args.pos fun snap => do
    let env := snap.cmdState.env
    if let some id := widgetSourceRegistry.getState env |>.find? args.hash then
      let d ← Lean.Server.RequestM.runCore snap <| getUserWidgetDefinition id
      return {sourcetext := d.javascript}
    else
      throw <| RequestError.mk .invalidParams s!"No registered user-widget with hash {args.hash}"

open Lean Elab

/--
  Try to retrieve the `UserWidgetInfo` at a particular position.
-/
def widgetInfosAt? (text : FileMap) (t : InfoTree) (hoverPos : String.Pos) : List UserWidgetInfo :=
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

/-- UserWidget accompanied by component props. -/
structure UserWidgetInstance extends UserWidget where
  /-- Arguments to be fed to the widget's main component. -/
  props : Json
  /-- The location of the widget instance in the Lean file. -/
  range? : Option Lsp.Range
  deriving ToJson, FromJson

/-- Output of `getWidgets` RPC.-/
structure GetWidgetsResponse where
  widgets : Array UserWidgetInstance
  deriving ToJson, FromJson

open Lean Server RequestM in
/-- Get the `UserWidget`s present at a particular position. -/
@[serverRpcMethod]
def getWidgets (args : Lean.Lsp.Position) : RequestM (RequestTask (GetWidgetsResponse)) := do
  let doc ← readDoc
  let filemap := doc.meta.text
  let pos := filemap.lspPosToUtf8Pos args
  withWaitFindSnapAtPos args fun snap => do
    let env := snap.env
    let ws := widgetInfosAt? filemap snap.infoTree pos
    let ws ← ws.toArray.mapM (fun (w : UserWidgetInfo) => do
      let some widget := userWidgetRegistry.find? env w.widgetId
        | throw <| RequestError.mk .invalidParams s!"No registered user-widget with id {w.widgetId}"
      return {
        widget with
        props := w.props
        range? := String.Range.toLspRange filemap <$> Syntax.getRange? w.stx
      })
    return {widgets := ws}

/-- Save a user-widget instance to the infotree.
    The given `widgetId` should be the declaration name of the widget definition. -/
def saveWidgetInfo [Monad m] [MonadEnv m] [MonadError m] [MonadInfoTree m] (widgetId : Name) (props : Json) (stx : Syntax):  m Unit := do
  let info := Info.ofUserWidgetInfo {
    widgetId := widgetId
    props := props
    stx := stx
  }
  pushInfoLeaf info

/-!  # Widget command

Use `#widget <widgetname> <props>` to display a widget.
-/

syntax (name := widgetCmd) "#widget " ident term : command

open Lean Lean.Meta Lean.Elab Lean.Elab.Term in
private unsafe def evalJsonUnsafe (stx : Syntax) : TermElabM Json :=
  Lean.Elab.Term.evalTerm Json (mkConst ``Json) stx

@[implementedBy evalJsonUnsafe]
private opaque evalJson (stx : Syntax) : TermElabM Json

open Elab Command in

/-- Use this to place a widget. Useful for debugging widgets. -/
@[commandElab widgetCmd] def elabWidgetCmd : CommandElab := fun
  | stx@`(#widget $id:ident $props) => do
    let props : Json ← runTermElabM none (fun _ => evalJson props)
    saveWidgetInfo id.getId props stx
  | _ => throwUnsupportedSyntax

end Lean.Widget
