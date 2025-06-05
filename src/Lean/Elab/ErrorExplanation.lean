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

open Lean Parser Term in
def expandThrowNamedError : Macro
  | `(throwNamedErrorParser| throwNamedError $id:ident $msg:interpolatedStr) =>
    ``(Lean.throwNamedError $(quote id.getId) m! $msg)
  | `(throwNamedErrorParser| throwNamedError $id $msg:term) =>
    ``(Lean.throwNamedError $(quote id.getId) $msg)
  | `(throwNamedErrorAtParser| throwNamedErrorAt $ref $id $msg:interpolatedStr) =>
    ``(Lean.throwNamedErrorAt $ref $(quote id.getId) m! $msg)
  | `(throwNamedErrorAtParser| throwNamedErrorAt $ref $id $msg:term) =>
    ``(Lean.throwNamedErrorAt $ref $(quote id.getId) $msg)
  | `(logNamedErrorParser| logNamedError $id $msg:interpolatedStr) =>
    ``(Lean.logNamedError $(quote id.getId) m! $msg)
  | `(logNamedErrorParser| logNamedError $id $msg:term) =>
    ``(Lean.logNamedError $(quote id.getId) $msg)
  | `(logNamedErrorAtParser| logNamedErrorAt $ref $id $msg:interpolatedStr) =>
    ``(Lean.logNamedErrorAt $ref $(quote id.getId) m! $msg)
  | `(logNamedErrorAtParser| logNamedErrorAt $ref $id $msg:term) =>
    ``(Lean.logNamedErrorAt $ref $(quote id.getId) $msg)
  | _ => Macro.throwUnsupported

open Lean Elab Term in
-- @[builtin_term_elab throwNamedErrorParser, builtin_term_elab throwNamedErrorAtParser,
--   builtin_term_elab logNamedErrorParser, builtin_term_elab logNamedErrorAtParser]
@[term_elab throwNamedErrorParser, term_elab throwNamedErrorAtParser,
  term_elab logNamedErrorParser, term_elab logNamedErrorAtParser]
def elabCheckedNamedError : TermElab := fun stx expType? => do
  let (id, numArgsExpected) := if stx.isOfKind ``Parser.Term.throwNamedErrorAtParser ||
               stx.isOfKind ``Parser.Term.logNamedErrorAtParser then
    (stx[2], 5)
  else
    (stx[1], 4)
  -- Remove the message term so the name is the penultimate argument per the `errorName` invariant.
  -- If we have a trailing `.`, we fail to parse the message term and so leave `stx` unchanged.
  let span := if stx.getNumArgs == numArgsExpected then
    stx.setArgs (stx.getArgs[0:stx.getNumArgs - 1])
  else
    stx
  addCompletionInfo <| CompletionInfo.errorName span
  let name := id.getId.eraseMacroScopes
  pushInfoLeaf <| .ofErrorNameInfo { stx := id, errorName := name }
  let some explan := getErrorExplanationRaw? (← getEnv) name
    | throwError m!"There is no explanation associated with the name `{name}`. \
      Add an explanation of this error to the `Lean.ErrorExplanation` module."
  if let some removedVersion := explan.metadata.removedVersion then
    logWarningAt id m!"The error name `{name}` was removed in Lean version {removedVersion} and \
      should not be used."
  let stx' ← liftMacroM <| expandThrowNamedError stx
  elabTerm stx' expType?

open Parser Elab Meta Term Command in
@[builtin_command_elab registerErrorExplanationStx] def elabRegisterErrorExplanation : CommandElab
| `(registerErrorExplanationStx| $docStx:docComment register_error_explanation%$cmd $id:ident $t:term) => withRef cmd do
  unless (← getEnv).contains ``Lean.ErrorExplanation do
    throwError "To use this command, add `import Lean.ErrorExplanation` to the header of this file"
  let tp := mkConst ``ErrorExplanation.Metadata []
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
  let (declLoc? : Option ErrorExplanation.Location) ← do
    let some uri ← Server.documentUriFromModule? (← getMainModule) | pure none
    let map ← getFileMap
    let start := map.utf8PosToLspPos <| id.raw.getPos?.getD 0
    let fin := id.raw.getTailPos?.map map.utf8PosToLspPos |>.getD start
    pure <| some {
      uri := (uri : String)
      rangeStart := (start.line, start.character)
      rangeEnd := (fin.line, fin.character)
    }
  modifyEnv (errorExplanationExt.addEntry · (name, { metadata, doc, declLoc? }))
| _ => throwUnsupportedSyntax
