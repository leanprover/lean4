import Lean.Elab.InfoTree
import Lean.Message
import Lean.Server.Rpc.Basic

namespace Lean.Widget

open Elab Server

/-- Expression with the context required to render it interactively in the infoview. -/
structure ExprWithCtx where
  ctx  : Elab.ContextInfo
  lctx : LocalContext
  expr : Expr
  deriving Inhabited, RpcEncoding with { withRef := true }
deriving instance RpcEncoding with { withRef := true } for MessageData

/-- Creates a dummy Elab.Info from an ExprWithCtx. -/
def ExprWithCtx.toTermInfo (e : ExprWithCtx) : Elab.Info :=
  Elab.Info.ofTermInfo {
    elaborator := Name.anonymous -- [todo] is this right?
    stx := Syntax.missing -- [todo] is this right?
    lctx := e.lctx
    expr := e.expr
    expectedType? := none
  }

instance : ToJson FVarId := ⟨fun f => toJson f.name⟩
instance : ToJson MVarId := ⟨fun f => toJson f.name⟩
instance : FromJson FVarId := ⟨fun j => FVarId.mk <$> fromJson? j⟩
instance : FromJson MVarId := ⟨fun j => MVarId.mk <$> fromJson? j⟩

end Lean.Widget
