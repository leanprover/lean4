/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
module

prelude
public import Lean.Server.Rpc.Basic

public section

namespace Lean.Widget

/-- An instance of a widget component:
the identifier of a widget module and the hash of its JS source code
together with props.

See the [manual entry](https://lean-lang.org/documentation/widgets/)
for more information about widgets. -/
structure WidgetInstance where
  /-- Name of the `@[widget_module]`. -/
  id : Name
  /-- Hash of the JS source of the widget module. -/
  javascriptHash : UInt64
  /-- Arguments to be passed to the component's default exported function.
  Must be a JSON object.

  In certain contexts
  (such as when rendering as a panel widget; see `Widget.savePanelWidgetInfo`),
  the Lean infoview appends additional fields to this object.

  Props may contain RPC references,
  so must be stored as a `StateM` computation
  with access to the RPC object store. -/
  props : StateM Server.RpcObjectStore Json
  deriving Server.RpcEncodable

/-- A widget module is a unit of source code that can execute in the infoview.

Every module definition must either be annotated with `@[widget_module]`,
or use a value of `javascript` identical to that of another definition
annotated with `@[widget_module]`.
This makes it possible for the infoview to load the module.

See the [manual entry](https://lean-lang.org/examples/1900-1-1-widgets/)
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

end Lean.Widget
