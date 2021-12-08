import Lean.Data.Json
import Lean.Data.JsonRpc
import Lean.Data.Lsp.Basic

namespace Lean
namespace Lsp
open Json

/-- How a signature help was triggered.-/
inductive SignatureHelpTriggerKind where
  | /-- Signature help was invoked manually by the user or by a command. -/
  Invoked
  | /-- Signature help was triggered by a trigger character. -/
  TriggerCharacter
  | /-- Signature help was triggered by the cursor moving or by the document content changing. -/
  ContentChange
  |
  Unknown

def signatureHelpTriggerKindFromInt (i : Int) :=
  match i with
  | 0 => SignatureHelpTriggerKind.Invoked
  | 1 => SignatureHelpTriggerKind.TriggerCharacter
  | 2 => SignatureHelpTriggerKind.ContentChange
  | _  => SignatureHelpTriggerKind.Unknown

instance : FromJson SignatureHelpTriggerKind := ⟨fun
  | str "invoked" => Except.ok SignatureHelpTriggerKind.Invoked
  | str "triggerCharacter"  => Except.ok SignatureHelpTriggerKind.TriggerCharacter
  | str "contentChange"  => Except.ok SignatureHelpTriggerKind.ContentChange
  | num (i : Int) => Except.ok (signatureHelpTriggerKindFromInt i)
  | _  => throw "unknown MarkupKind"⟩

instance : ToJson SignatureHelpTriggerKind := ⟨fun
  | SignatureHelpTriggerKind.Invoked => str "invoked"
  | SignatureHelpTriggerKind.TriggerCharacter => str "triggerCharacter"
  | SignatureHelpTriggerKind.ContentChange  => str "contentChange"
  | SignatureHelpTriggerKind.Unknown  => str "unknown"⟩

/--  Either a string or an inclusive start and exclusive end offsets within
  its containing signature label. The offsets are based on a UTF-16 string
  representation as `Position` and `Range` does. -/
inductive ParameterLabel where
  | label : String -> ParameterLabel
  | range : Range -> ParameterLabel
  deriving FromJson, ToJson

/--
  Represents a parameter of a callable-signature. A parameter can
  have a label and a doc-comment.
-/
structure ParameterInformation where
  /-
   The label of this parameter.

   Either a string or an inclusive start and exclusive end offsets within
   its containing signature label. (see SignatureInformation.label). The
   offsets are based on a UTF-16 string representation as `Position` and
   `Range` does.

   *Note*: a label of type string should be a substring of its containing
   signature label. Its intended use case is to highlight the parameter
   label part in the `SignatureInformation.label`. -/
  label: ParameterLabel

  /-- The human-readable doc-comment of this parameter. Will be shown
  in the UI but can be omitted. -/
  documentation?: Option String := none
  deriving FromJson, ToJson

/--
Represents the signature of something callable. A signature
can have a label, like a function-name, a doc-comment, and
a set of parameters. -/
structure SignatureInformation where
  /-- The label of this signature. Will be shown in the UI. -/
  label: String
  /-- The human-readable doc-comment of this signature. Will be shown
  in the UI but can be omitted. -/
  documentation?: Option String := none
  /-- The parameters of this signature. -/
  parameters?: Option (List ParameterInformation) := none
  /-- The index of the active parameter. If provided, this is used
  in place of `SignatureHelp.activeParameter`.-/
  activeParameter? : Option Nat := none
  deriving FromJson, ToJson

/-- Signature help represents the signature of something
 callable. There can be multiple signatures but only one
 active and only one active parameter.-/
structure SignatureHelp where
  /-- One or more signatures. If no signatures are available the signature
  help request should return `null`. -/
  signatures: List SignatureInformation := []
  /-- The active signature. If omitted or the value lies outside the
  range of `signatures` the value defaults to none or is ignored if
  the `SignatureHelp` has no signatures.

  Whenever possible implementors should make an active decision about
  the active signature and shouldn't rely on a default value.

  In future versions of the protocol this property might become
  mandatory to better express this.-/
  activeSignature?: Option Int := none
  /--
  The active parameter of the active signature. If omitted or the value
  lies outside the range of `signatures[activeSignature].parameters`
  defaults to 0 if the active signature has parameters. If
  the active signature has no parameters it is ignored.
  In future versions of the protocol this property might become
  mandatory to better express the active parameter if the
  active signature does have any. -/
  activeParameter?: Option Nat := none
  deriving FromJson, ToJson

/--  Additional information about the context in which a signature help request
was triggered.-/
structure SignatureHelpContext where
  /-- Action that caused signature help to be triggered.-/
  triggerKind: SignatureHelpTriggerKind
  /-- Character that caused signature help to be triggered.
  This is undefined when triggerKind !== TriggerCharacter -/
  triggerCharacter?: Option String := none
  /-- `true` if signature help was already showing when it was triggered.
  Retriggers occur when the signature help is already active and can be
  caused by actions such as typing a trigger character, a cursor move, or
  document content changes.  -/
  isRetrigger: Bool
  /-- The currently active `SignatureHelp`.
  The `activeSignatureHelp` has its `SignatureHelp.activeSignature` field
  updated based on the user navigating through available signatures. -/
  activeSignatureHelp?: Option SignatureHelp := none
  deriving FromJson, ToJson

/-- The object returned in response to a `textDocument/signatureHelp` request -/
structure SignatureHelpParams extends TextDocumentPositionParams, WorkDoneProgressParams where
  /--
  The signature help context. This is only available if the client
  specifies to send this using the client capability
  `textDocument.signatureHelp.contextSupport === true` -/
  context? : Option SignatureHelpContext := none
  deriving FromJson, ToJson

structure SignatureHelpOptions extends WorkDoneProgressOptions where
  /--
  The characters that trigger signature help automatically.
  -/
  triggerCharacters : Array String := #[]

  /--
   List of characters that re-trigger signature help.

   These trigger characters are only active when signature help is already
   showing. All trigger characters are also counted as re-trigger
   characters.
  -/
  retriggerCharacters : Array String := #[]
  deriving FromJson, ToJson

structure SignatureHelpParameterInformation where
  /--
  The client supports processing label offsets instead of a
  simple label string. -/
  labelOffsetSupport?: Option Bool
  deriving FromJson, ToJson

structure SignatureHelpSignatureInformation where
  /--
  Client supports the follow content formats for the documentation
  property. The order describes the preferred format of the client.
  -/
  documentationFormat: List MarkupKind := []

  /--
  Client capabilities specific to parameter information.
  -/
  parameterInformation?: Option SignatureHelpParameterInformation := none

  /--
  The client supports the `activeParameter` property on
  `SignatureInformation` literal. -/
  activeParameterSupport?: Option Bool := none
  deriving FromJson, ToJson

structure SignatureHelpClientCapabilities where
  /--
  Whether signature help supports dynamic registration.
  -/
  dynamicRegistration?: Option Bool := none

  /--
  The client supports the following `SignatureInformation`
  specific properties.
  -/
  signatureInformation?: Option SignatureHelpSignatureInformation := none

  /--
  The client supports to send additional context information for a
  `textDocument/signatureHelp` request. A client that opts into
  contextSupport will also support the `retriggerCharacters` on
  `SignatureHelpOptions`. -/
  contextSupport?: Option Bool := none
  deriving FromJson, ToJson
