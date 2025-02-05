/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.Command
set_option linter.missingDocs true -- keep it documented

/-!
This file defines style linters for the `List`/`Array`/`Vector` modules.

Currently, we do not anticipate that they will be useful elsewhere.
-/

/--
`set_option linter.index_variables true` enables a strict linter that
validates that the only variables appearing as an index (e.g. in `xs[i]` or `xs.take i`)
are `i`, `j`, or `k`.
-/
register_builtin_option linter.index_variables : Bool := {
  defValue := false
  descr := "Validate that variables appearing as an index (e.g. in `xs[i]` or `xs.take i`) are only `i`, `j`, or `k`."
}

open Lean Elab Command

/-- Return the syntax for the arguments of all "numerical indices" appearing in the given syntax. -/
partial def numericalIndices (stx : Syntax) : Array Syntax :=
  if stx.isOfKind ``«term__[_]» || stx.isOfKind ``«term__[_]'_» then
    #[stx[2]]
  else if stx.isOfKind ``«term__[_]_?» then
    #[stx[3]]
  else
    stx.getArgs.flatMap numericalIndices

/--
A linter which validates that the only variables used as "indices" (e.g. in `xs[i]` or `xs.take i`)
are `i`, `j`, or `k`.
-/
def indexLinter : Linter
  where run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.index_variables (← getOptions) do return
    if (← get).messages.hasErrors then return
    for idxStx in numericalIndices stx do
      if idxStx.isIdent then
        let ident := idxStx.getId
        if ident != `i && ident != `j && ident != `k then
          Linter.logLint linter.index_variables idxStx
            m!"Forbidden variable appearing as an index: use `i`, `j`, or `k`: {ident}"

builtin_initialize addLinter indexLinter
#eval `(term| xs.drop i)
