import Lean.Elab.InfoTree
import Lean.Message
import Lean.Server.Rpc.Basic

namespace Lean.Widget

open Elab Server

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
  deriving Inhabited, Std.TypeName

deriving instance Std.TypeName for MessageData

instance : ToJson FVarId := ⟨fun f => toJson f.name⟩
instance : ToJson MVarId := ⟨fun f => toJson f.name⟩
instance : FromJson FVarId := ⟨fun j => FVarId.mk <$> fromJson? j⟩
instance : FromJson MVarId := ⟨fun j => MVarId.mk <$> fromJson? j⟩

end Lean.Widget
