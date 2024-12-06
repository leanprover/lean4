/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers, Wojciech Nawrocki
-/
prelude
import Lean.Elab.Eval
import Lean.Server.Rpc.RequestHandling

namespace Lean.Widget
open Meta Elab

/-- A widget module is a unit of source code that can execute in the infoview.

Every module definition must either be annotated with `@[widget_module]`,
or use a value of `javascript` identical to that of another definition
annotated with `@[widget_module]`.
This makes it possible for the infoview to load the module.

See the [manual entry](https://lean-lang.org/lean4/doc/examples/widgets.lean.html)
for more information on how to use the widgets system. -/
structure Module where
  /-- A JS [module](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Modules)
  intended for use in user widgets.

  The JS environment in which modules execute
  provides a fixed set of libraries accessible via direct `import`,
  notably [`@leanprover/infoview`](https://www.npmjs.com/package/@leanprover/infoview)
  and [`react`](https://www.npmjs.com/package/react).

  To initialize this field from an external JS file,
  you may use `include_str "path"/"to"/"file.js"`.
  However **beware** that this does not register a dependency with Lake,
  so your Lean module will not automatically be rebuilt
  when the `.js` file changes. -/
  javascript : String
  /-- The hash is cached to avoid recomputing it whenever the `Module` is used. -/
  javascriptHash : { x : UInt64 // x = hash javascript } := ⟨hash javascript, rfl⟩

private unsafe def evalModuleUnsafe (e : Expr) : MetaM Module :=
  evalExpr' Module ``Module e

@[implemented_by evalModuleUnsafe]
opaque evalModule (e : Expr) : MetaM Module

private unsafe def evalWidgetInstanceUnsafe (e : Expr) : MetaM WidgetInstance :=
  evalExpr' WidgetInstance ``WidgetInstance e

@[implemented_by evalWidgetInstanceUnsafe]
opaque evalWidgetInstance (e : Expr) : MetaM WidgetInstance

/-! ## Storage of widget modules -/

class ToModule (α : Type u) where
  toModule : α → Module

instance : ToModule Module := ⟨id⟩

private builtin_initialize builtinModulesRef : IO.Ref (RBMap UInt64 (Name × Module) compare) ←
  IO.mkRef ∅

def addBuiltinModule (id : Name) (m : Module) : IO Unit :=
  builtinModulesRef.modify (·.insert m.javascriptHash (id, m))

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

/-- Registers a widget module. Its type must implement `Lean.Widget.ToModule`. -/
builtin_initialize widgetModuleAttrImpl : AttributeImpl ←
  let mkAttr (builtin : Bool) (name : Name) := do
    let impl := {
      name
      descr           := (if builtin then "(builtin) " else "") ++
        "Registers a widget module. Its type must implement Lean.Widget.ToModule."
      applicationTime := .afterCompilation
      add             := fun decl stx kind => Prod.fst <$> MetaM.run do
        Attribute.Builtin.ensureNoArgs stx
        unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
        let e ← mkAppM ``ToModule.toModule #[.const decl []]
        let mod ← evalModule e
        let env ← getEnv
        unless builtin do  -- don't warn on collision between previous and current stage
          if let some _ := (← builtinModulesRef.get).find? mod.javascriptHash then
            logWarning m!"A builtin widget module with the same hash(JS source code) was already registered."
        if let some (n, _) := moduleRegistry.getState env |>.find? mod.javascriptHash then
          logWarning m!"A widget module with the same hash(JS source code) was already registered at {.ofConstName n true}."
        let env ← getEnv
        if builtin then
          let h := mkConst decl
          declareBuiltin decl <| mkApp2 (mkConst ``addBuiltinModule) (toExpr decl) h
        else
          setEnv <| moduleRegistry.addEntry env (mod.javascriptHash, decl, e)
    }
    registerBuiltinAttribute impl
    return impl
  /- We declare the `[builtin_widget_module]` and `[widget_module]` attributes
  and bind the latter's implementation
  (used for creating the obsolete `[widget]` alias below). -/
  let _ ← mkAttr true `builtin_widget_module
  mkAttr false `widget_module

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
def getWidgetSource (args : GetWidgetSourceParams) : RequestM (RequestTask WidgetSource) := do
  if let some (_, m) := (← builtinModulesRef.get).find? args.hash then
    return .pure { sourcetext := m.javascript }

  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos args.pos
  let notFound := throwThe RequestError ⟨.invalidParams, s!"No widget module with hash {args.hash} registered"⟩
  withWaitFindSnap doc (notFoundX := notFound)
    (fun s => s.endPos >= pos || (moduleRegistry.getState s.env).contains args.hash)
    fun snap => do
      if let some (_, e) := moduleRegistry.getState snap.env |>.find? args.hash then
        runTermElabM snap do
          return { sourcetext := (← evalModule e).javascript }
      else
        notFound

builtin_initialize
  Server.registerBuiltinRpcProcedure ``getWidgetSource _ _ getWidgetSource

/-! ## Storage of panel widget instances -/

inductive PanelWidgetsExtEntry where
  | «global» (n : Name)
  | «local» (wi : WidgetInstance)

/-- Keeps track of panel widget instances that should be displayed.

Instances can be registered for display global
(i.e., persisted in `.olean`s) and locally (not persisted)

For globally displayed widgets
we cannot store a `WidgetInstance` in the persistent state
because it contains a `StateM` closure.
Instead, we add a global constant of type `WidgetInstance`
to the environment, and store its name in the extension.

For locally displayed ones, we just store a `WidgetInstance`
in the extension directly.
This is okay because it is never persisted.

The (persistent) entries are then of the form `(h, n)`
where `h` is a hash stored in the `moduleRegistry`
and `n` is the name of a `WidgetInstance` global constant.

The extension state maps each `h` as above
to a list of entries that can be either global or local ones.
Each element of the state indicates that the widget module `h`
should be displayed with the given `WidgetInstance` as its arguments.

This is similar to a parametric attribute, except that:
- parametric attributes map at most one parameter to one tagged declaration,
  whereas we may display multiple instances of a single widget module; and
- parametric attributes use the same type for local and global entries,
  which we cannot do owing to the closure. -/
private abbrev PanelWidgetsExt := SimpleScopedEnvExtension
  (UInt64 × Name)
  (RBMap UInt64 (List PanelWidgetsExtEntry) compare)

builtin_initialize panelWidgetsExt : PanelWidgetsExt ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s (h, n) => s.insert h (.global n :: s.findD h [])
    initial  := .empty
  }

def evalPanelWidgets : MetaM (Array WidgetInstance) := do
  let mut ret := #[]
  for (_, l) in panelWidgetsExt.getState (← getEnv) do
    for e in l do
      match e with
      | .global n =>
        let wi ← evalWidgetInstance (mkConst n)
        ret := ret.push wi
      | .local wi => ret := ret.push wi
  return ret

def addPanelWidgetGlobal [Monad m] [MonadEnv m] [MonadResolveName m] (h : UInt64) (n : Name) : m Unit := do
  panelWidgetsExt.add (h, n)

def addPanelWidgetScoped [Monad m] [MonadEnv m] [MonadResolveName m] (h : UInt64) (n : Name) : m Unit := do
  panelWidgetsExt.add (h, n) .scoped

def addPanelWidgetLocal [Monad m] [MonadEnv m] (wi : WidgetInstance) : m Unit := do
  modifyEnv fun env => panelWidgetsExt.modifyState env fun s =>
    s.insert wi.javascriptHash (.local wi :: s.findD wi.javascriptHash [])

def erasePanelWidget [Monad m] [MonadEnv m] (h : UInt64) : m Unit := do
  modifyEnv fun env => panelWidgetsExt.modifyState env fun st => st.erase h

/-- Construct a widget instance by finding a widget module
in the current environment.

`hash` must be `hash (toModule c).javascript`
where `c` is some global constant annotated with `@[widget_module]`,
or the name of a builtin widget module. -/
def WidgetInstance.ofHash (hash : UInt64) (props : StateM Server.RpcObjectStore Json) :
    CoreM WidgetInstance := do
  let env ← getEnv
  let builtins ← builtinModulesRef.get
  let some id :=
    (builtins.find? hash |>.map (·.1)) <|> (moduleRegistry.getState env |>.find? hash |>.map (·.1))
    | throwError s!"No widget module with hash {hash} registered"
  return { id, javascriptHash := hash, props }

/-- Save the data of a panel widget which will be displayed whenever the text cursor is on `stx`.

`hash` must be as in `WidgetInstance.ofHash`. -/
def savePanelWidgetInfo (hash : UInt64) (props : StateM Server.RpcObjectStore Json) (stx : Syntax) :
    CoreM Unit := do
  let wi ← WidgetInstance.ofHash hash props
  pushInfoLeaf <| .ofUserWidgetInfo { wi with stx }

/-! ## `show_panel_widgets` command -/

syntax widgetInstanceSpec := ident ("with " term)?

def elabWidgetInstanceSpecAux (mod : Ident) (props : Term) : TermElabM Expr := do
  Term.elabTerm (expectedType? := mkConst ``WidgetInstance) <| ← `(
    { id := $(quote mod.getId)
      javascriptHash := (ToModule.toModule $mod).javascriptHash
      props := Server.RpcEncodable.rpcEncode $props })

def elabWidgetInstanceSpec : TSyntax ``widgetInstanceSpec → TermElabM Expr
  | `(widgetInstanceSpec| $mod:ident) => do
    elabWidgetInstanceSpecAux mod (← ``(Json.mkObj []))
  | `(widgetInstanceSpec| $mod:ident with $props:term) => do
    elabWidgetInstanceSpecAux mod props
  | _ => throwUnsupportedSyntax

syntax addWidgetSpec := Parser.Term.attrKind widgetInstanceSpec
syntax eraseWidgetSpec := "-" ident
syntax showWidgetSpec := addWidgetSpec <|> eraseWidgetSpec
/-- Use `show_panel_widgets [<widget>]` to mark that `<widget>`
should always be displayed, including in downstream modules.

The type of `<widget>` must implement `Widget.ToModule`,
and the type of `<props>` must implement `Server.RpcEncodable`.
In particular, `<props> : Json` works.

Use `show_panel_widgets [<widget> with <props>]`
to specify the `<props>` that the widget should be given
as arguments.

Use `show_panel_widgets [local <widget> (with <props>)?]` to mark it
for display in the current section, namespace, or file only.

Use `show_panel_widgets [scoped <widget> (with <props>)?]` to mark it
for display only when the current namespace is open.

Use `show_panel_widgets [-<widget>]` to temporarily hide a previously shown widget
in the current section, namespace, or file.
Note that persistent erasure is not possible, i.e.,
`-<widget>` has no effect on downstream modules. -/
syntax (name := showPanelWidgetsCmd) "show_panel_widgets " "[" sepBy1(showWidgetSpec, ", ") "]" : command

open Command in
@[command_elab showPanelWidgetsCmd] def elabShowPanelWidgetsCmd : CommandElab
  | `(show_panel_widgets [ $ws ,*]) => liftTermElabM do
    for w in ws.getElems do
      match w with
      | `(showWidgetSpec| - $mod:ident) =>
        let mod : Term ← ``(ToModule.toModule $mod)
        let mod : Expr ← Term.elabTerm (expectedType? := mkConst ``Module) mod
        let mod : Module ← evalModule mod
        erasePanelWidget mod.javascriptHash
      | `(showWidgetSpec| $attr:attrKind $spec:widgetInstanceSpec) =>
        let attr ← liftMacroM <| toAttributeKind attr
        let wiExpr ← elabWidgetInstanceSpec spec
        let wi ← evalWidgetInstance wiExpr
        if let .local := attr then
          addPanelWidgetLocal wi
        else
          let name ← mkFreshUserName (wi.id ++ `_instance)
          let wiExpr ← instantiateMVars wiExpr
          if wiExpr.hasMVar then
            throwError "failed to compile expression, it contains metavariables{indentExpr wiExpr}"
          addAndCompile <| Declaration.defnDecl {
            name
            levelParams := []
            type := mkConst ``WidgetInstance
            value := wiExpr
            hints := .opaque
            safety := .safe
          }
          if let .global := attr then
            addPanelWidgetGlobal wi.javascriptHash name
          else
            addPanelWidgetScoped wi.javascriptHash name
      | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

/-! ## `#widget` command -/

/-- Use `#widget <widget>` to display a panel widget,
and `#widget <widget> with <props>` to display it with the given props.
Useful for debugging widgets.

The type of `<widget>` must implement `Widget.ToModule`,
and the type of `<props>` must implement `Server.RpcEncodable`.
In particular, `<props> : Json` works. -/
syntax (name := widgetCmd) "#widget " widgetInstanceSpec : command

open Command in
@[command_elab widgetCmd] def elabWidgetCmd : CommandElab
  | stx@`(#widget $s) => liftTermElabM do
    let wi : Expr ← elabWidgetInstanceSpec s
    let wi : WidgetInstance ← evalWidgetInstance wi
    savePanelWidgetInfo wi.javascriptHash wi.props stx
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

private unsafe def evalUserWidgetDefinitionUnsafe [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m]
    (id : Name) : m UserWidgetDefinition := do
  ofExcept <| (← getEnv).evalConstCheck UserWidgetDefinition (← getOptions) ``UserWidgetDefinition id

@[implemented_by evalUserWidgetDefinitionUnsafe]
opaque evalUserWidgetDefinition [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m]
    (id : Name) : m UserWidgetDefinition

/-! ## Retrieving panel widget instances -/

/-- Retrieve all the `UserWidgetInfo`s that intersect a given line. -/
def widgetInfosAt? (text : FileMap) (t : InfoTree) (hoverLine : Nat) : List UserWidgetInfo :=
  t.deepestNodes fun
    | _ctx, i@(Info.ofUserWidgetInfo wi), _cs => do
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        -- Does the widget's line range contain `hoverLine`?
        guard <| (text.utf8PosToLspPos pos).line ≤ hoverLine ∧ hoverLine ≤ (text.utf8PosToLspPos tailPos).line
        return wi
      else
        failure
    | _, _, _ => none

structure PanelWidgetInstance extends WidgetInstance where
  /-- The syntactic span in the Lean file at which the panel widget is displayed. -/
  range? : Option Lsp.Range := none
  /-- When present, the infoview will wrap the widget
  in `<details><summary>{name}</summary>...</details>`.
  This functionality is deprecated
  but retained for backwards compatibility
  with `UserWidgetDefinition`. -/
  name? : Option String := none
  deriving Server.RpcEncodable

/-- Output of `getWidgets` RPC.-/
structure GetWidgetsResponse where
  widgets : Array PanelWidgetInstance
  deriving Server.RpcEncodable

open Lean Server RequestM in
/-- Get the panel widgets present around a particular position. -/
def getWidgets (pos : Lean.Lsp.Position) : RequestM (RequestTask (GetWidgetsResponse)) := do
  let doc ← readDoc
  let filemap := doc.meta.text
  mapTask (findInfoTreeAtPosWithTrailingWhitespace doc <| filemap.lspPosToUtf8Pos pos) fun
    | some infoTree@(.context (.commandCtx cc) _) =>
      ContextInfo.runMetaM { cc with } {} do
      let env ← getEnv
      /- Panels from the environment. -/
      let ws' ← evalPanelWidgets
      let ws' : Array PanelWidgetInstance ← ws'.mapM fun wi => do
        -- Check if the definition uses the deprecated `UserWidgetDefinition`
        -- on a best-effort basis.
        -- If it does, also send the `name` field.
        let name? ← env.find? wi.id
          |>.filter (·.type.isConstOf ``UserWidgetDefinition)
          |>.mapM fun _ => do
            let uwd ← evalUserWidgetDefinition wi.id
            return uwd.name
        return { wi with name? }
      /- Panels from the infotree. -/
      let ws := widgetInfosAt? filemap infoTree pos.line
      let ws : Array PanelWidgetInstance ← ws.toArray.mapM fun (wi : UserWidgetInfo) => do
        let name? ← env.find? wi.id
          |>.filter (·.type.isConstOf ``UserWidgetDefinition)
          |>.mapM fun _ => do
            let uwd ← evalUserWidgetDefinition wi.id
            return uwd.name
        return { wi with range? := String.Range.toLspRange filemap <$> Syntax.getRange? wi.stx, name? }
      return { widgets := ws' ++ ws }
    | _ => return ⟨∅⟩

builtin_initialize
  Server.registerBuiltinRpcProcedure ``getWidgets _ _ getWidgets

end Lean.Widget
