/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Message
import Lean.InternalExceptionId

namespace Lean

/- Exception type used in most Lean monads -/
inductive Exception
| error (ref : Syntax) (msg : MessageData)
| internal (id : InternalExceptionId)

def Exception.toMessageData : Exception → MessageData
| Exception.error _ msg => msg
| Exception.internal id => id.toString

def Exception.getRef : Exception → Syntax
| Exception.error ref _ => ref
| Exception.internal _  => Syntax.missing

instance Exception.inhabited : Inhabited Exception := ⟨Exception.error (arbitrary _) (arbitrary _)⟩

end Lean
