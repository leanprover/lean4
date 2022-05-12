import Lean.Elab.InfoTree
import Lean.Message
import Lean.Server.Rpc.Basic

namespace Lean.Widget

open Elab Server

deriving instance RpcEncoding with { withRef := true } for Expr
deriving instance RpcEncoding with { withRef := true } for LocalContext
deriving instance RpcEncoding with { withRef := true } for ContextInfo
deriving instance RpcEncoding with { withRef := true } for Info
deriving instance RpcEncoding with { withRef := true } for MessageData

end Lean.Widget
