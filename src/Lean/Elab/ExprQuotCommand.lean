/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Elab.ExprQuot

public section

namespace Lean.Elab.Command

/--
Command elaborator for `#check_pattern `(expr[rel]| p)`.

Lives in its own module above `Lean.Elab.Command` and `Lean.Elab.ExprQuot` so
`Lean.Elab.BuiltinCommand` does not depend on `expr` quotation machinery.
-/
@[builtin_command_elab Lean.Parser.Command.checkPattern]
def elabCheckPattern : CommandElab := fun stx => do
  unless stx.isOfKind ``Lean.Parser.Command.checkPattern && stx.getNumArgs >= 2 do
    throwUnsupportedSyntax
  let tk := stx[0]
  let term := stx[1]
  withoutModifyingEnv <| runTermElabM fun vars => Term.withDeclName `_checkPattern do
    let msg ← withRef tk <| Term.ExprQuot.inspectExprQuotPattern vars term
    logInfoAt tk msg

end Lean.Elab.Command
