import Lean.Elab.InfoTree
import Lean.Message
import Lean.Server.Rpc.Basic

namespace Lean.Widget

open Elab Server

structure ExprWithCtx where
  ctx  : Elab.ContextInfo
  lctx : LocalContext
  expr : Expr
  deriving Inhabited, RpcEncoding with { withRef := true }

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
