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
  /-- The hash is cached to avoid recomputing it whenever the `Module` is used. -/
  javascriptHash : { x : UInt64 // x = hash javascript } := ⟨hash javascript, rfl⟩

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
    let env ← getEnv
    if let some (n, _) := moduleRegistry.getState env |>.find? mod.javascriptHash then
      logWarning m!"A widget module with the same hash(JS source code) was already registered at {Expr.const n []}."
    setEnv <| moduleRegistry.addEntry env (mod.javascriptHash, decl, e)

builtin_initialize registerBuiltinAttribute widgetModuleAttrImpl

/-! ## Retrieval of widget modules -/

structure GetWidgetSourceParams where
  /-- Hash of the JS module to retrieve. -/
  hash : UInt64
  pos : Lean.Lsp.Position
  deriving ToJson, FromJson

structure WidgetSource where
  /-- Sourcetext of the JS module to run. -/
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


/-! ## Retrieving panel widget instances -/

#mkrpcenc WidgetInstance

/-- Save the data of a panel widget which will be displayed whenever the text cursor is on `stx`.
`hash` must be `hash (toModule c).javascript`
where `c` is some global constant annotated with `@[widget_module]`. -/
def savePanelWidgetInfo [Monad m] [MonadEnv m] [MonadError m] [MonadInfoTree m]
    (hash : UInt64) (props : StateM Server.RpcObjectStore Json) (stx : Syntax) : m Unit := do
  let env ← getEnv
  let some (id, _) := moduleRegistry.getState env |>.find? hash
    | throwError s!"No widget module with hash {hash} registered"
  pushInfoLeaf <| .ofPanelWidgetInfo { id, javascriptHash := hash, props, stx }

/-- Retrieve all the `PanelWidgetInfo`s at a particular position. -/
def widgetInfosAt? (text : FileMap) (t : InfoTree) (hoverPos : String.Pos) : List PanelWidgetInfo :=
  t.deepestNodes fun
    | _ctx, i@(Info.ofPanelWidgetInfo wi), _cs => do
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        let trailSize := i.stx.getTrailingSize
        -- show info at EOF even if strictly outside token + trail
        let atEOF := tailPos.byteIdx + trailSize == text.source.endPos.byteIdx
        guard <| pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + trailSize || atEOF)
        return wi
      else
        failure
    | _, _, _ => none

structure PanelWidgetInstance extends WidgetInstance where
  /-- The syntactic span in the Lean file at which the panel widget is displayed. -/
  range? : Option Lsp.Range
  /-- Deprecated. Kept for compatibility with older infoviews. -/
  name? : Option String := none
#mkrpcenc PanelWidgetInstance

/-- Output of `getWidgets` RPC.-/
structure GetWidgetsResponse where
  widgets : Array PanelWidgetInstance
#mkrpcenc GetWidgetsResponse

open Lean Server RequestM in
/-- Get the panel widgets present at a particular position. -/
@[server_rpc_method]
def getWidgets (args : Lean.Lsp.Position) : RequestM (RequestTask (GetWidgetsResponse)) := do
  let doc ← readDoc
  let filemap := doc.meta.text
  let pos := filemap.lspPosToUtf8Pos args
  withWaitFindSnap doc (·.endPos >= pos) (notFoundX := return ⟨∅⟩) fun snap => do
    let ws := widgetInfosAt? filemap snap.infoTree pos
    let ws ← ws.toArray.mapM (fun (wi : PanelWidgetInfo) => do
      return { wi with
        range? := String.Range.toLspRange filemap <$> Syntax.getRange? wi.stx
        name? := toString wi.id
      })
    return {widgets := ws}

/-! # Widget command -/

/-- Use `#widget <widget>` to display a panel widget,
and `#widget <widget> with <props>` to display it with the given props.
Useful for debugging widgets.

The type of `<widget>` must implement `Widget.ToModule`,
and the type of `<props>` must implement `Server.RpcEncodable`.
In particular, `<props> : Json` works. -/
syntax (name := widgetCmd) "#widget " ident (" with " term)? : command

private unsafe def evalStateMRpcObjectStoreJsonUnsafe (stx : Term) :
    TermElabM (StateM Server.RpcObjectStore Json) := do
  Lean.Elab.Term.evalTerm _
    (← mkAppM ``StateM #[mkConst ``Server.RpcObjectStore, mkConst ``Json])
    stx

@[implemented_by evalStateMRpcObjectStoreJsonUnsafe]
private opaque evalStateMRpcObjectStoreJson (stx : Term) :
    TermElabM (StateM Server.RpcObjectStore Json)

private unsafe def evalModule'Unsafe (stx : Term) : TermElabM Module := do
  Lean.Elab.Term.evalTerm _ (mkConst ``Module) stx

@[implemented_by evalModule'Unsafe]
private opaque evalModule' (stx : Term) : TermElabM Module

open Command in
def elabWidgetCmdAux (stx : Syntax) (mod : Ident) (props : StateM Server.RpcObjectStore Json)
    : CommandElabM Unit := do
  let mod  ← runTermElabM fun _ => do
    let mod : Term ← ``(ToModule.toModule $mod)
    evalModule' mod
  savePanelWidgetInfo mod.javascriptHash props stx

open Command in
@[command_elab widgetCmd] def elabWidgetCmd : CommandElab := fun
  | stx@`(#widget $mod) => elabWidgetCmdAux stx mod (pure Json.null)
  | stx@`(#widget $mod with $props) => do
    let props ← runTermElabM fun _ => do
      let props : Term ← ``(Server.RpcEncodable.rpcEncode $props)
      evalStateMRpcObjectStoreJson props
    elabWidgetCmdAux stx mod props
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

private def widgetAttrImpl : AttributeImpl where
  name := `widget
  descr := "The `@[widget]` attribute has been deprecated, use `@[widget_module]` instead."
  applicationTime := AttributeApplicationTime.afterCompilation
  add := widgetModuleAttrImpl.add

builtin_initialize registerBuiltinAttribute widgetAttrImpl

private unsafe def evalUserWidgetDefinitionUnsafe [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m]
    (id : Name) : m UserWidgetDefinition := do
  ofExcept <| (← getEnv).evalConstCheck UserWidgetDefinition (← getOptions) ``UserWidgetDefinition id

@[implemented_by evalUserWidgetDefinitionUnsafe]
private opaque evalUserWidgetDefinition [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m]
    (id : Name) : m UserWidgetDefinition

/-- Save a user-widget instance to the infotree.
    The given `widgetId` should be the declaration name of the widget definition. -/
@[deprecated savePanelWidgetInfo] def saveWidgetInfo
    [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadInfoTree m]
    (widgetId : Name) (props : Json) (stx : Syntax) : m Unit := do
  let uwd ← evalUserWidgetDefinition widgetId
  savePanelWidgetInfo (ToModule.toModule uwd).javascriptHash (pure props) stx

attribute [deprecated Module] UserWidgetDefinition

end Lean.Widget
