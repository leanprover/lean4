/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.KeyedDeclsAttribute

namespace Lean
namespace PrettyPrinter

/- Auxiliary internal exception for backtracking the pretty printer.
   See `orelse.parenthesizer` for example -/
builtin_initialize backtrackExceptionId : InternalExceptionId ← registerInternalExceptionId `backtrackFormatter

unsafe def runForNodeKind {α} (attr : KeyedDeclsAttribute α) (k : SyntaxNodeKind) (interp : ParserDescr → CoreM α) : CoreM α := do
  match attr.getValues (← getEnv) k with
  | p::_ => pure p
  | _ =>
    -- assume `k` is from a `ParserDescr`, in which case we assume it's also the declaration name
    let info ← getConstInfo k
    if info.type.isConstOf ``ParserDescr || info.type.isConstOf ``TrailingParserDescr then
      let d ← evalConst ParserDescr k
      interp d
    else
      throwError "no declaration of attribute [{attr.defn.name}] found for '{k}'"

end PrettyPrinter
end Lean
