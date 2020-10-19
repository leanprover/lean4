/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.InternalExceptionId

namespace Lean
namespace PrettyPrinter

/- Auxiliary internal exception for backtracking the pretty printer.
   See `orelse.parenthesizer` for example -/
def registerBacktrackId : IO InternalExceptionId := registerInternalExceptionId `backtrackFormatter
@[builtinInit registerBacktrackId] constant backtrackExceptionId : InternalExceptionId := arbitrary _

end PrettyPrinter
end Lean
