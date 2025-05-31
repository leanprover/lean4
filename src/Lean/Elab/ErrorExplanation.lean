prelude
import Lean.ErrorExplanation
import Lean.Meta.Eval
import Lean.Elab.Term
import Lean.Elab.Command
import Lean.Widget.UserWidget
import Std.Internal.Parsec

namespace Lean.Elab.ErrorExplanation

-- We cannot import the definitions needed for this attribute in `Lean.Log`, so we instead add it
-- here
attribute [builtin_widget_module] Lean.errorDescriptionWidget

-- TODO: the following QoL features would be very helpful (i > ii -- probably i >> ii):
-- (i) cmd-click on error names to jump to the explanation   <-- Could labeled sorries be a model?
-- (ii) autocomplete with registered error explanation names

open Lean Parser Term in
def expandThrowNamedError : Macro
  | `(throwNamedErrorParser| throwNamedError $id:ident $msg:interpolatedStr) => ``(Lean.throwNamedError $(quote id.getId) m! $msg)
  | `(throwNamedErrorParser| throwNamedError $id $msg:term) => ``(Lean.throwNamedError $(quote id.getId) $msg)
  | `(throwNamedErrorAtParser| throwNamedErrorAt $ref $id $msg:interpolatedStr) => ``(Lean.throwNamedErrorAt $ref $(quote id.getId) m! $msg)
  | `(throwNamedErrorAtParser| throwNamedErrorAt $ref $id $msg:term) => ``(Lean.throwNamedErrorAt $ref $(quote id.getId) $msg)
  | `(logNamedErrorParser| logNamedError $id $msg:interpolatedStr) => ``(Lean.logNamedError $(quote id.getId) m! $msg)
  | `(logNamedErrorParser| logNamedError $id $msg:term) => ``(Lean.logNamedError $(quote id.getId) $msg)
  | `(logNamedErrorAtParser| logNamedErrorAt $ref $id $msg:interpolatedStr) => ``(Lean.logNamedErrorAt $ref $(quote id.getId) m! $msg)
  | `(logNamedErrorAtParser| logNamedErrorAt $ref $id $msg:term) => ``(Lean.logNamedErrorAt $ref $(quote id.getId) $msg)
  | _ => Macro.throwUnsupported

open Lean Elab Term in
-- @[builtin_term_elab throwNamedErrorParser, builtin_term_elab throwNamedErrorAtParser,
--   builtin_term_elab logNamedErrorParser, builtin_term_elab logNamedErrorAtParser]
@[term_elab throwNamedErrorParser, term_elab throwNamedErrorAtParser,
  term_elab logNamedErrorParser, term_elab logNamedErrorAtParser]
def elabCheckedNamedError : TermElab
  | stx@`(throwNamedError $id:ident $_msg), expType?
  | stx@`(throwNamedErrorAt $_ref $id:ident $_msg), expType?
  | stx@`(logNamedError $id:ident $_msg), expType?
  | stx@`(logNamedErrorAt $_ref $id:ident $_msg), expType? => do
    logInfo m!"Calling elabCheckedNamedError; adding completion info with syntax {stx.setArgs (stx.getArgs[0:stx.getNumArgs - 1])}"
    logInfo m!"Sanity check: is the ref equal to `stx`? {(← getRef) == stx}"
    let name := id.getId
    -- The message is unnecessary for completion:
    addCompletionInfo <| CompletionInfo.errorName (stx.setArgs (stx.getArgs[0:stx.getNumArgs - 1]))
    pushInfoLeaf <| .ofErrorNameInfo { stx := id, errorName := name}
    let some explan := getErrorExplanationRaw? (← getEnv) name
      | throwError m!"There is no explanation associated with the name `{name}`. \
        Add an explanation of this error to the `Lean.ErrorExplanation` module."
    if let some removedVersion := explan.metadata.removedVersion then
      logWarningAt id m!"The error name `{name}` was removed in Lean version {removedVersion} and \
        should not be used."
    let stx' ← liftMacroM <| expandThrowNamedError stx
    elabTerm stx' expType?
  | _, _ => throwUnsupportedSyntax

open Parser Elab Meta Term Command in
@[builtin_command_elab registerErrorExplanationStx] def elabRegisterErrorExplanation : CommandElab
| `(registerErrorExplanationStx| $docStx:docComment register_error_explanation%$cmd $nm:ident $t:term) => withRef cmd do
  unless (← getEnv).contains ``Lean.ErrorExplanation do
    throwError "To use this command, add `import Lean.ErrorExplanation` to the header of this file"
  let tp := mkConst ``ErrorExplanation.Metadata []
  let metadata ← runTermElabM <| fun _ => unsafe do
    let e ← elabTerm t tp
    if e.hasSyntheticSorry then throwAbortTerm
    evalExpr ErrorExplanation.Metadata tp e
  let name := nm.getId
  if name.isAnonymous then
    throwErrorAt nm "Invalid name for error explanation: `{nm}`"
  if name.getNumParts != 2 then
    throwErrorAt nm m!"Invalid name `{nm}`: Error explanation names must have two components"
      ++ .note m!"The first component of an error explanation name identifies the package from \
        which the error originates, and the second identifies the error itself."
  validateDocComment docStx
  let doc ← getDocStringText docStx
  if errorExplanationExt.getState (← getEnv) |>.contains name then
    throwErrorAt nm m!"Cannot add explanation: An error explanation already exists for `{name}`"
  let codeBlocks ←
    match ErrorExplanation.processDoc doc with
    | .ok bs => pure bs
    | .error (lineOffset, msg) =>
      let some range := docStx.raw[1].getRange? | throwError msg
      let fileMap ← getFileMap
      let ⟨startLine, _⟩ := fileMap.toPosition range.start
      let errLine := startLine + lineOffset
      let synth := Syntax.ofRange { start := fileMap.ofPosition ⟨errLine, 0⟩,
                                    stop  := fileMap.ofPosition ⟨errLine + 1, 0⟩ }
      throwErrorAt synth msg
  modifyEnv (errorExplanationExt.addEntry · (name, { metadata, doc, codeBlocks }))
| _ => throwUnsupportedSyntax
