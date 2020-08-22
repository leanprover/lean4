/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.MetavarContext
import Lean.Message
import Lean.CoreM
import Lean.InternalExceptionId
import Lean.Util.PPGoal

namespace Lean
namespace Meta

def registerIsDefEqStuckId : IO InternalExceptionId :=
registerInternalExceptionId `isDefEqStuck

@[init registerIsDefEqStuckId]
constant isDefEqStuckExceptionId : InternalExceptionId := arbitrary _

end Meta
end Lean
