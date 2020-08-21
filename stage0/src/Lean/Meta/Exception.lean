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
| isDefEqStuck
| core          (ex : Core.Exception)

namespace Exception
instance : Inhabited Exception := ⟨core $ arbitrary _⟩

def getRef : Exception → Syntax
| core ex => ex.ref
| _       => Syntax.missing

def mkCtx (ctx : ExceptionContext) (m : MessageData) : MessageData :=
MessageData.withContext ctx m

def toMessageData : Exception → MessageData
| isDefEqStuck => "<isDefEqStuck>"
| core ex      => ex.toMessageData

end Exception

end Meta
end Lean
