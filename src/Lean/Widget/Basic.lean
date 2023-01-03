import Lean.Elab.InfoTree
import Lean.Message
import Lean.Server.Rpc.Basic
import Lean.Server.InfoUtils

namespace Lean.Widget

open Elab Server

deriving instance TypeName for InfoWithCtx
deriving instance TypeName for MessageData

instance : ToJson FVarId := ⟨fun f => toJson f.name⟩
instance : ToJson MVarId := ⟨fun f => toJson f.name⟩
instance : FromJson FVarId := ⟨fun j => FVarId.mk <$> fromJson? j⟩
instance : FromJson MVarId := ⟨fun j => MVarId.mk <$> fromJson? j⟩

end Lean.Widget
