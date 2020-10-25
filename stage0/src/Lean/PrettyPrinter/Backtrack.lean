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
builtin_initialize backtrackExceptionId : InternalExceptionId ← registerInternalExceptionId `backtrackFormatter

end PrettyPrinter
end Lean
