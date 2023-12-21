/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Server.Rpc.Basic

namespace Lean.Widget

/-- An instance of a widget component:
the identifier of a widget module and the hash of its JS source code
together with props.

See the [manual entry](https://lean-lang.org/lean4/doc/examples/widgets.lean.html)
for more information about widgets. -/
structure WidgetInstance where
  /-- Name of the `@[widget_module]`. -/
  id : Name
  /-- Hash of the JS source of the widget module. -/
  javascriptHash : UInt64
  /-- Arguments to be passed to the component's default exported function.

  Props may contain RPC references,
  so must be stored as a computation
  with access to the RPC object store. -/
  props : StateM Server.RpcObjectStore Json

end Lean.Widget
