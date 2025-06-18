/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
prelude
import Lean.ErrorExplanation
import Lean.Meta.Eval
import Lean.Elab.Term
import Lean.Elab.Command
import Lean.Widget.UserWidget

namespace Lean.Elab.ErrorExplanation

open Meta Parser Term

-- We cannot import the definitions needed for this attribute in `Lean.Log`, so we instead add it
-- here
attribute [builtin_widget_module] Lean.errorDescriptionWidget

def expandNamedErrorMacro : Macro
  | `(throwNamedErrorMacro| throwNamedError $id:ident $msg:interpolatedStr) =>
    ``(Lean.throwNamedError $(quote id.getId) m! $msg)
  | `(throwNamedErrorMacro| throwNamedError $id $msg:term) =>
    ``(Lean.throwNamedError $(quote id.getId) $msg)
  | `(throwNamedErrorAtMacro| throwNamedErrorAt $ref $id $msg:interpolatedStr) =>
    ``(Lean.throwNamedErrorAt $ref $(quote id.getId) m! $msg)
  | `(throwNamedErrorAtMacro| throwNamedErrorAt $ref $id $msg:term) =>
    ``(Lean.throwNamedErrorAt $ref $(quote id.getId) $msg)
  | `(logNamedErrorMacro| logNamedError $id $msg:interpolatedStr) =>
    ``(Lean.logNamedError $(quote id.getId) m! $msg)
  | `(logNamedErrorMacro| logNamedError $id $msg:term) =>
    ``(Lean.logNamedError $(quote id.getId) $msg)
  | `(logNamedErrorAtMacro| logNamedErrorAt $ref $id $msg:interpolatedStr) =>
    ``(Lean.logNamedErrorAt $ref $(quote id.getId) m! $msg)
  | `(logNamedErrorAtMacro| logNamedErrorAt $ref $id $msg:term) =>
    ``(Lean.logNamedErrorAt $ref $(quote id.getId) $msg)
  | `(logNamedWarningMacro| logNamedWarning $id $msg:interpolatedStr) =>
    ``(Lean.logNamedWarning $(quote id.getId) m! $msg)
  | `(logNamedWarningMacro| logNamedWarning $id $msg:term) =>
    ``(Lean.logNamedWarning $(quote id.getId) $msg)
  | `(logNamedWarningAtMacro| logNamedWarningAt $ref $id $msg:interpolatedStr) =>
    ``(Lean.logNamedWarningAt $ref $(quote id.getId) m! $msg)
  | `(logNamedWarningAtMacro| logNamedWarningAt $ref $id $msg:term) =>
    ``(Lean.logNamedWarningAt $ref $(quote id.getId) $msg)
  | _ => Macro.throwUnsupported

/--
Maps macro syntax categories to a pair of the module containing the declaration on which the macro
depends and the name of that declaration.
-/
private def macroDeclMap :=
  Std.HashMap.ofList
    [(``throwNamedErrorMacro, (`Lean.Exception, ``Lean.throwNamedError)),
     (``throwNamedErrorAtMacro, (`Lean.Exception, ``Lean.throwNamedErrorAt)),
     (``logNamedErrorMacro, (`Lean.Log, ``Lean.logNamedError)),
     (``logNamedErrorAtMacro, (`Lean.Log, ``Lean.logNamedErrorAt)),
     (``logNamedWarningMacro, (`Lean.Log, ``Lean.logNamedWarning)),
     (``logNamedWarningAtMacro, (`Lean.Log, ``Lean.logNamedWarningAt))]

@[builtin_term_elab throwNamedErrorMacro, builtin_term_elab throwNamedErrorAtMacro,
  builtin_term_elab logNamedErrorMacro, builtin_term_elab logNamedErrorAtMacro,
  builtin_term_elab logNamedWarningMacro, builtin_term_elab logNamedWarningAtMacro]
def elabCheckedNamedError : TermElab := fun stx expType? => do
  if let some (module, decl) := macroDeclMap.get? stx.getKind then
    if !(← getEnv).contains decl then
      throwError m!"The constant `{decl}` has not been imported" ++
        .hint' m!"Add `import {module}` to this file's header to use this macro"
  let (id, numArgsExpected) :=
    if stx.isOfKind ``throwNamedErrorAtMacro || stx.isOfKind ``logNamedErrorAtMacro
        || stx.isOfKind ``logNamedWarningAtMacro then
    (stx[2], 5)
  else
    (stx[1], 4)
  -- Remove the message term from the span. If we have a trailing `.`, we fail to parse the message
  -- term and so leave `stx` unchanged. The in-progress identifier will always be the penultimate
  -- argument of `span`.
  let span := if stx.getNumArgs == numArgsExpected then
    stx.setArgs (stx.getArgs[0:stx.getNumArgs - 1])
  else
    stx
  let partialId := span[span.getNumArgs - 2]
  addCompletionInfo <| CompletionInfo.errorName span partialId
  let name := id.getId.eraseMacroScopes
  pushInfoLeaf <| .ofErrorNameInfo { stx := id, errorName := name }
  if let some explan := getErrorExplanationRaw? (← getEnv) name then
    if let some removedVersion := explan.metadata.removedVersion? then
      logWarningAt id m!"The error name `{name}` was removed in Lean version {removedVersion} and \
        should not be used."
  else
    logErrorAt id m!"There is no explanation associated with the name `{name}`. \
      Add an explanation of this error to the `Lean.ErrorExplanations` module."
  let stx' ← liftMacroM <| expandNamedErrorMacro stx
  elabTerm stx' expType?

open Command in
@[builtin_command_elab registerErrorExplanationStx] def elabRegisterErrorExplanation : CommandElab
| `(registerErrorExplanationStx| $docStx:docComment register_error_explanation%$cmd $id:ident $t:term) => withRef cmd do
  unless (← getEnv).contains ``Lean.ErrorExplanation do
    throwError "To use this command, add `import Lean.ErrorExplanation` to the header of this file"
  let tp := mkConst ``ErrorExplanation.Metadata
  let metadata ← runTermElabM <| fun _ => unsafe do
    let e ← elabTerm t tp
    if e.hasSyntheticSorry then throwAbortTerm
    evalExpr ErrorExplanation.Metadata tp e
  let name := id.getId
  if name.isAnonymous then
    throwErrorAt id "Invalid name for error explanation: `{id}`"
  if name.hasMacroScopes then
    -- Use `id` rather than `name` for nicer rendering
    throwErrorAt id m!"Invalid name `{id}`: Error explanations cannot have inaccessible names. \
      This error often occurs when an error explanation is generated using a macro."
  if name.getNumParts != 2 then
    throwErrorAt id m!"Invalid name `{name}`: Error explanation names must have two components"
      ++ .note m!"The first component of an error explanation name identifies the package from \
        which the error originates, and the second identifies the error itself."
  validateDocComment docStx
  let doc ← getDocStringText docStx
  if errorExplanationExt.getState (← getEnv) |>.contains name then
    throwErrorAt id m!"Cannot add explanation: An error explanation already exists for `{name}`"
  if let .error (lineOffset, msg) := ErrorExplanation.processDoc doc then
    let some range := docStx.raw[1].getRange? | throwError msg
    let fileMap ← getFileMap
    let ⟨startLine, _⟩ := fileMap.toPosition range.start
    let errLine := startLine + lineOffset
    let synth := Syntax.ofRange { start := fileMap.ofPosition ⟨errLine, 0⟩,
                                  stop  := fileMap.ofPosition ⟨errLine + 1, 0⟩ }
    throwErrorAt synth msg
  let (declLoc? : Option DeclarationLocation) ← do
    let map ← getFileMap
    let start := id.raw.getPos?.getD 0
    let fin := id.raw.getTailPos?.getD start
    pure <| some {
      module := (← getMainModule)
      range := .ofStringPositions map start fin
    }
  modifyEnv (errorExplanationExt.addEntry · (name, { metadata, doc, declLoc? }))
| _ => throwUnsupportedSyntax
