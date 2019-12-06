/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta

namespace Lean
namespace Elab

inductive Exception
| io     : IO.Error → Exception
| msg    : Message → Exception
| kernel : KernelException → Exception
| meta   : Meta.Exception → Exception
| other  : String → Exception
/- Elab.Exception.silent is used when we log an error in `messages`, and then
   want to interrupt the elaborator execution. We use it to make sure the
   top-level handler does not record it again in `messages`. See `logErrorAndThrow` -/
| silent : Exception

instance Exception.inhabited : Inhabited Exception := ⟨Exception.silent⟩

end Elab
end Lean
