import Lean.Elab.InfoTree
import Lean.Message
import Lean.Server.Rpc.Basic

namespace Lean.Widget

open Elab Server

/-- Expression with the context required to render it interactively in the infoview.

The difference with `InfoWithCtx` is that this is an explicitly an expression which is not necessarily created during the elaboration step.

The purpose of `ExprWithCtx` is so that widget writers can send an expression over and display it,
as well as send it back in another RPC call for further processing.
The former functionality can be achieved by sending `CodeWithInfos`, and even the latter could by inspecting the root tag for its `.ofTermInfo`.
However `ExprWithCtx` gives a cleaner interface, and it gives the option to not pretty-print the expression,
which can be useful if the widget code just needs it around as data, or wants to delay printing until the user requests it.
-/
structure ExprWithCtx where
  ctx  : Elab.ContextInfo
  lctx : LocalContext
  expr : Expr
  deriving Inhabited, RpcEncoding with { withRef := true }

/-- Elaborator information with elaborator context.

This is used to tag different parts of expressions in `ppExprTagged`.
This is the input to the RPC call `Lean.Widget.InteractiveDiagnostics.infoToInteractive`.

The purpose of `InfoWithCtx` is to carry over information about delaborated
`Info` nodes in a `CodeWithInfos`, and the associated pretty-printing
functionality is purpose-specific to showing the contents of infoview popups.
-/
structure InfoWithCtx where
  ctx  : Elab.ContextInfo
  info : Elab.Info
  deriving Inhabited, RpcEncoding with { withRef := true }

deriving instance RpcEncoding with { withRef := true } for MessageData

instance : ToJson FVarId := ⟨fun f => toJson f.name⟩
instance : ToJson MVarId := ⟨fun f => toJson f.name⟩
instance : FromJson FVarId := ⟨fun j => FVarId.mk <$> fromJson? j⟩
instance : FromJson MVarId := ⟨fun j => MVarId.mk <$> fromJson? j⟩

end Lean.Widget
