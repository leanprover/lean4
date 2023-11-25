/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers, Wojciech Nawrocki
-/
import Lean.Elab.Eval
import Lean.Server.Rpc.RequestHandling

namespace Lean.Server
open Elab Command in
/-- Derive `Lean.Server.RpcEncodable` for a type.

TODO: remove after update-stage0 -/
elab "#mkrpcenc" n:ident : command => do
  elabCommand <| ← `(
    namespace $n
    deriving instance Lean.Server.RpcEncodable for $n
    end $n
  )
end Lean.Server

namespace Lean.Widget
open Meta Elab

/-! ## Storage of widget modules -/

/-- A widget module is a unit of source code that can execute in the infoview.

See the [manual entry](https://lean-lang.org/lean4/doc/examples/widgets.lean.html)
for more information on how to use the widgets system. -/
structure Module where
  /-- A JS [module](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Modules)
  intended for use in user widgets.

  To initialize this field from an external JS file,
  you may use `include_str "path"/"to"/"file.js"`.
  However **beware** that this does not register a dependency with Lake,
  so your Lean module will not automatically be rebuilt
  when the `.js` file changes. -/
  javascript : String

class ToModule (α : Type u) where
  toModule : α → Module

instance : ToModule Module := ⟨id⟩

/-- Every constant `c : α` marked with `@[widget_module]` is registered here.
The registry maps `hash (toModule c).javascript` to ``(`c, `(@toModule α inst c))``
where `inst : ToModule α` is synthesized during registration time
and stored thereafter. -/
private abbrev ModuleRegistry := SimplePersistentEnvExtension
  (UInt64 × Name × Expr)
  (RBMap UInt64 (Name × Expr) compare)

builtin_initialize moduleRegistry : ModuleRegistry ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun xss => xss.foldl (Array.foldl (fun s n => s.insert n.1 n.2)) ∅
    addEntryFn    := fun s n => s.insert n.1 n.2
    toArrayFn     := fun es => es.toArray
  }

private unsafe def evalModuleUnsafe (e : Expr) : MetaM Module :=
  evalExpr' Module ``Module e

@[implemented_by evalModuleUnsafe]
private opaque evalModule (e : Expr) : MetaM Module

private def widgetModuleAttrImpl : AttributeImpl where
  name := `widget_module
  descr := "Registers a widget module. Its type must implement Lean.Widget.ToModule."
  applicationTime := AttributeApplicationTime.afterCompilation
  add decl _stx _kind := Prod.fst <$> MetaM.run do
    let e ← mkAppM ``ToModule.toModule #[.const decl []]
    let mod ← evalModule e
    let javascriptHash := hash mod.javascript
    let env ← getEnv
    if let some (n, _) := moduleRegistry.getState env |>.find? javascriptHash then
      logWarning m!"A widget module with the same hash(JS source code) was already registered at {Expr.const n []}."
    setEnv <| moduleRegistry.addEntry env (javascriptHash, decl, e)

builtin_initialize registerBuiltinAttribute widgetModuleAttrImpl

/-! ## Retrieval of widget modules -/

structure GetWidgetSourceParams where
  /-- The hash of the sourcetext to retrieve. -/
  hash: UInt64
  pos : Lean.Lsp.Position
  deriving ToJson, FromJson

structure WidgetSource where
  /-- Sourcetext of the code to run.-/
  sourcetext : String
  deriving Inhabited, ToJson, FromJson

open Server RequestM in
@[server_rpc_method]
def getWidgetSource (args : GetWidgetSourceParams) : RequestM (RequestTask WidgetSource) := do
  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos args.pos
  let notFound := throwThe RequestError ⟨.invalidParams, s!"No widget module with hash {args.hash} registered"⟩
  withWaitFindSnap doc (notFoundX := notFound)
    (fun s => s.endPos >= pos || (moduleRegistry.getState s.env).contains args.hash)
    fun snap => do
      if let some (_, e) := moduleRegistry.getState snap.env |>.find? args.hash then
        runTermElabM snap do
          return {sourcetext := (← evalModule e).javascript}
      else
        notFound

/-! ## Saving panel widget info -/

structure UserWidget where
  id : Name
  /-- Pretty name of widget to display to the user. -/
  name : String
  javascriptHash: UInt64
  deriving Inhabited, ToJson, FromJson

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
@[server_rpc_method]
def getWidgets (args : Lean.Lsp.Position) : RequestM (RequestTask (GetWidgetsResponse)) := do
  let doc ← readDoc
  let filemap := doc.meta.text
  let pos := filemap.lspPosToUtf8Pos args
  withWaitFindSnap doc (·.endPos >= pos) (notFoundX := return ⟨∅⟩) fun snap => do
    let env := snap.env
    let ws := widgetInfosAt? filemap snap.infoTree pos
    let ws ← ws.toArray.mapM (fun (w : UserWidgetInfo) => do
      for (h, n, _) in moduleRegistry.getState env do
        if n == w.widgetId then
          return {
            id := w.widgetId
            name := toString w.widgetId
            javascriptHash := h
            props := w.props
            range? := String.Range.toLspRange filemap <$> Syntax.getRange? w.stx
          }
      throw <| RequestError.mk .invalidParams s!"No registered user-widget with id {w.widgetId}")
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

/-!  # Widget command -/

/-- Use `#widget <widgetname> <props>` to display a widget. Useful for debugging widgets. -/
syntax (name := widgetCmd) "#widget " ident ppSpace term : command

open Lean Lean.Meta Lean.Elab Lean.Elab.Term in
private unsafe def evalJsonUnsafe (stx : Syntax) : TermElabM Json :=
  Lean.Elab.Term.evalTerm Json (mkConst ``Json) stx

@[implemented_by evalJsonUnsafe]
private opaque evalJson (stx : Syntax) : TermElabM Json

open Elab Command in

@[command_elab widgetCmd] def elabWidgetCmd : CommandElab := fun
  | stx@`(#widget $id:ident $props) => do
    let props : Json ← runTermElabM fun _ => evalJson props
    saveWidgetInfo id.getId props stx
  | _ => throwUnsupportedSyntax

/-! ## Deprecated definitions -/

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

instance : ToModule UserWidgetDefinition where
  toModule uwd := { uwd with }

attribute [deprecated Module] UserWidgetDefinition

private def widgetAttrImpl : AttributeImpl where
  name := `widget
  descr := "The `@[widget]` attribute has been deprecated, use `@[widget_module]` instead."
  applicationTime := AttributeApplicationTime.afterCompilation
  add := widgetModuleAttrImpl.add

builtin_initialize registerBuiltinAttribute widgetAttrImpl

end Lean.Widget
