/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.MetavarContext
import Lean.Message
import Lean.CoreM
import Lean.Util.PPGoal

namespace Lean
namespace Meta

abbrev ExceptionContext := MessageDataContext

inductive Exception
| isLevelDefEqStuck (u v : Level) (ctx : ExceptionContext)
| isExprDefEqStuck  (t s : Expr) (ctx : ExceptionContext)
| core              (ex : Core.Exception)

instance EIOEx.monadIO : MonadIO (EIO Exception) :=
mkEIOMonadIO Exception.core

namespace Exception
instance : Inhabited Exception := ⟨core $ arbitrary _⟩

def getRef : Exception → Syntax
| core (Core.Exception.error ref _) => ref
| _                                 => Syntax.missing

def mkCtx (ctx : ExceptionContext) (m : MessageData) : MessageData :=
MessageData.withContext ctx m

/-- Generate trace message that is suitable for tracing crawlers -/
def toTraceMessageData : Exception → MessageData
| isLevelDefEqStuck u v ctx       => mkCtx ctx $ `isLevelDefEqStuck ++ " " ++ u ++ " =?= " ++ v
| isExprDefEqStuck t s ctx        => mkCtx ctx $ `isExprDefEqStuck ++ " " ++ t ++ " =?= " ++ s
| core ex                         => ex.toMessageData

def toMessageData : Exception → MessageData
| isLevelDefEqStuck u v ctx       => mkCtx ctx $ `isLevelDefEqStuck ++ " " ++ u ++ " =?= " ++ v
| isExprDefEqStuck t s ctx        => mkCtx ctx $ `isExprDefEqStuck ++ " " ++ t ++ " =?= " ++ s
| core ex                         => ex.toMessageData

end Exception

end Meta
end Lean
