/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.Sorry
import Lean.Widget.Types
import Lean.Message
import Lean.DocString.Links
-- This import is necessary to ensure that any users of the `logNamedError` macros have access to
-- all declared explanations:
import Lean.ErrorExplanations

namespace Lean

/--
The `MonadLog` interface for logging error messages.
-/
class MonadLog (m : Type → Type) extends MonadFileMap m where
  /-- Return the current reference syntax being used to provide position information. -/
  getRef       : m Syntax
  /-- The name of the file being processed. -/
  getFileName  : m String
  /-- Return `true` if errors have been logged. -/
  hasErrors    : m Bool
  /-- Log a new message. -/
  logMessage   : Message → m Unit

export MonadLog (getFileName logMessage)

instance (m n) [MonadLift m n] [MonadLog m] : MonadLog n where
  getRef      := liftM (MonadLog.getRef : m _)
  getFileMap  := liftM (getFileMap : m _)
  getFileName := liftM (getFileName : m _)
  hasErrors   := liftM (MonadLog.hasErrors : m _)
  logMessage  := fun msg => liftM (logMessage msg : m _ )

variable [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]

/--
Return the position (as `String.pos`) associated with the current reference syntax (i.e., the syntax object returned by `getRef`.)
-/
def getRefPos : m String.Pos := do
  let ref ← MonadLog.getRef
  return ref.getPos?.getD 0

/--
Return the line and column numbers associated with the current reference syntax (i.e., the syntax object returned by `getRef`.)
-/
def getRefPosition : m Position := do
  let fileMap ← getFileMap
  return fileMap.toPosition (← getRefPos)

/-- If `warningAsError` is set to `true`, then warning messages are treated as errors. -/
register_builtin_option warningAsError : Bool := {
  defValue := false
  descr    := "treat warnings as errors"
}

/--
A widget for displaying error names and explanation links.
-/
-- Note that we cannot tag this as a `builtin_widget_module` in this module because doing so would
-- create circular imports. Instead, we add this attribute post-hoc in `Lean.ErrorExplanation`.
def errorDescriptionWidget : Widget.Module where
  javascript := "
import { createElement } from 'react';
export default function ({ code, explanationUrl }) {
  const sansText = { fontFamily: 'var(--vscode-font-family)' }

  const codeSpan = createElement('span', {}, [
    createElement('span', { style: sansText }, 'Error code: '), code])
  const brSpan = createElement('span', {}, '\\n')
  const linkSpan = createElement('span', { style: sansText },
    createElement('a', { href: explanationUrl }, 'View explanation'))

  const all = createElement('div', { style: { marginTop: '1em' } }, [codeSpan, brSpan, linkSpan])
  return all
}"

/--
If `msg` is tagged as a named error, appends the error description widget displaying the
corresponding error name and explanation link. Otherwise, returns `msg` unaltered.
-/
private def MessageData.appendDescriptionWidgetIfNamed (msg : MessageData) : MessageData :=
  match errorNameOfKind? msg.kind with
  | some errorName =>
    let url := manualRoot ++ s!"find/?domain={errorExplanationManualDomain}&name={errorName}"
    let inst := {
      id := ``errorDescriptionWidget
      javascriptHash := errorDescriptionWidget.javascriptHash
      props := return json% {
        code: $(toString errorName),
        explanationUrl: $url
      }
    }
    -- Note: we do not generate corresponding message data for the widget because it pollutes
    -- console output
    msg.composePreservingKind <| .ofWidget inst .nil
  | none => msg

/--
Log the message `msgData` at the position provided by `ref` with the given `severity`.
If `getRef` has position information but `ref` does not, we use `getRef`.
We use the `fileMap` to find the line and column numbers for the error message.
-/
def logAt (ref : Syntax) (msgData : MessageData)
    (severity : MessageSeverity := MessageSeverity.error) (isSilent : Bool := false) : m Unit :=
  unless severity == .error && msgData.hasSyntheticSorry do
    let severity := if severity == .warning && warningAsError.get (← getOptions) then .error else severity
    let ref    := replaceRef ref (← MonadLog.getRef)
    let pos    := ref.getPos?.getD 0
    let endPos := ref.getTailPos?.getD pos
    let fileMap ← getFileMap
    -- TODO: change to `msgData.appendDescriptionWidgetIfNamed` once error explanation support is
    -- added to the manual
    let msgData ← addMessageContext msgData
    logMessage {
      fileName := (← getFileName)
      pos := fileMap.toPosition pos
      endPos := fileMap.toPosition endPos
      data := msgData
      severity
      isSilent
    }

/-- Log a new error message using the given message data. The position is provided by `ref`. -/
def logErrorAt (ref : Syntax) (msgData : MessageData) : m Unit :=
  logAt ref msgData MessageSeverity.error

/--
Log a named error message using the given message data. The position is provided by `ref`.

Note: Use the macro `logNamedErrorAt`, which validates error names, instead of calling this function
directly.
-/
protected def «logNamedErrorAt» (ref : Syntax) (name : Name) (msgData : MessageData) : m Unit :=
  logAt ref (msgData.tagWithErrorName name) MessageSeverity.error

/-- Log a new warning message using the given message data. The position is provided by `ref`. -/
def logWarningAt [MonadOptions m] (ref : Syntax) (msgData : MessageData) : m Unit := do
  logAt ref msgData .warning

/--
Log a named error warning using the given message data. The position is provided by `ref`.

Note: Use the macro `logNamedWarningAt`, which validates error names, instead of calling this function
directly.
-/
protected def «logNamedWarningAt» (ref : Syntax) (name : Name) (msgData : MessageData) : m Unit :=
  logAt ref (msgData.tagWithErrorName name) MessageSeverity.warning

/-- Log a new information message using the given message data. The position is provided by `ref`. -/
def logInfoAt (ref : Syntax) (msgData : MessageData) : m Unit :=
  logAt ref msgData MessageSeverity.information

/-- Log a new error/warning/information message using the given message data and `severity`. The position is provided by `getRef`. -/
def log (msgData : MessageData) (severity : MessageSeverity := MessageSeverity.error)
    (isSilent : Bool := false) : m Unit := do
  let ref ← MonadLog.getRef
  logAt ref msgData severity isSilent

/-- Log a new error message using the given message data. The position is provided by `getRef`. -/
def logError (msgData : MessageData) : m Unit :=
  log msgData MessageSeverity.error

/--
Log a named error message using the given message data. The position is provided by `getRef`.

Note: Use the macro `logNamedError`, which validates error names, instead of calling this function
directly.
-/
protected def «logNamedError» (name : Name) (msgData : MessageData) : m Unit :=
  log (msgData.tagWithErrorName name) MessageSeverity.error

/-- Log a new warning message using the given message data. The position is provided by `getRef`. -/
def logWarning [MonadOptions m] (msgData : MessageData) : m Unit := do
  log msgData .warning

/--
Log a named warning using the given message data. The position is provided by `getRef`.

Note: Use the macro `logNamedWarning`, which validates error names, instead of calling this function
directly.
-/
protected def «logNamedWarning» (name : Name) (msgData : MessageData) : m Unit :=
  log (msgData.tagWithErrorName name) MessageSeverity.warning

/-- Log a new information message using the given message data. The position is provided by `getRef`. -/
def logInfo (msgData : MessageData) : m Unit :=
  log msgData MessageSeverity.information

/-- Log the error message "unknown declaration" -/
def logUnknownDecl (declName : Name) : m Unit :=
  logError m!"unknown declaration '{declName}'"

end Lean
