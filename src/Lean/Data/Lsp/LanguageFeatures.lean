/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Lsp.Basic
public import Lean.Expr
public import Init.Data.String.Search
public import Init.Data.Array.GetLit

public section

namespace Lean
namespace Lsp

open Json

structure CompletionOptions where
  triggerCharacters?   : Option (Array String) := none
  allCommitCharacters? : Option (Array String) := none
  resolveProvider      : Bool := false
  deriving FromJson, ToJson

inductive CompletionItemKind where
  | text | method | function | constructor | field
  | variable | class | interface | module | property
  | unit | value | enum | keyword | snippet
  | color | file | reference | folder | enumMember
  | constant | struct | event | operator | typeParameter
  deriving Inhabited, DecidableEq, Repr, Hashable

instance : ToJson CompletionItemKind where
  toJson a := toJson (a.ctorIdx + 1)

instance : FromJson CompletionItemKind where
  fromJson? v := do
    let i : Nat ← fromJson? v
    return CompletionItemKind.ofNat (i-1)

structure InsertReplaceEdit where
  newText : String
  insert  : Range
  replace : Range
  deriving FromJson, ToJson, BEq, Hashable

inductive CompletionItemTag where
  | deprecated
  deriving Inhabited, DecidableEq, Repr, Hashable

instance : ToJson CompletionItemTag where
  toJson t := toJson (t.ctorIdx + 1)

instance : FromJson CompletionItemTag where
  fromJson? v := do
    let i : Nat ← fromJson? v
    return CompletionItemTag.ofNat (i-1)

structure CompletionItem where
  -- When adjusting this type, make sure to adjust `ResolvableCompletionList.compressFast`
  -- as well, which is our `(toJson l).compress` fast path.
  -- (Completion downstream of Mathlib can output gigantic JSON,
  -- so we want to avoid all redundant allocs)
  label          : String
  detail?        : Option String := none
  documentation? : Option MarkupContent := none
  kind?          : Option CompletionItemKind := none
  textEdit?      : Option InsertReplaceEdit := none
  sortText?      : Option String := none
  data?          : Option Json := none
  tags?          : Option (Array CompletionItemTag) := none
  /-
  deprecated? : boolean
  preselect? : boolean
  filterText? : string
  insertText? : string
  insertTextFormat? : InsertTextFormat
  insertTextMode? : InsertTextMode
  additionalTextEdits? : TextEdit[]
  commitCharacters? : string[]
  command? : Command
  -/
  deriving FromJson, ToJson, Inhabited, BEq, Hashable

structure CompletionList where
  isIncomplete : Bool
  items        : Array CompletionItem
  deriving FromJson, ToJson

/--
Identifier that is sent from the server to the client as part of the `CompletionItem.data?` field.
Needed to resolve the `CompletionItem` when the client sends a `completionItem/resolve` request
for that item, again containing the `data?` field provided by the server.
-/
inductive CompletionIdentifier where
  | const (declName : Name)
  | fvar (id : Lean.FVarId)
  deriving BEq, Hashable

instance : ToJson CompletionIdentifier where
  toJson
  | .const declName =>
    .str s!"c{toString declName}"
  | .fvar id =>
    .str s!"f{toString id.name}"

instance : FromJson CompletionIdentifier where
  fromJson?
    | .str s =>
      let c := s.front
      if c == 'c' then
        let declName := String.Pos.Raw.extract s ⟨1⟩ s.rawEndPos |>.toName
        .ok <| .const declName
      else if c == 'f' then
        let id := ⟨String.Pos.Raw.extract s ⟨1⟩ s.rawEndPos |>.toName⟩
        .ok <| .fvar id
      else
        .error "Expected string with prefix `c` or `f` in `FromJson` instance of `CompletionIdentifier`."
    | _ => .error "Expected string in `FromJson` instance of `CompletionIdentifier`."

structure ResolvableCompletionItemData where
  uri   : DocumentUri
  pos   : Position
  /-- Position of the completion info that this completion item was created from. -/
  cPos? : Option Nat := none
  id?   : Option CompletionIdentifier := none
  deriving BEq, Hashable

instance : ToJson ResolvableCompletionItemData where
  toJson d := Id.run do
    let mut arr : Array Json := #[
      toJson d.uri,
      d.pos.line,
      d.pos.character,
    ]
    if let some cPos := d.cPos? then
      arr := arr.push <| toJson cPos
    if let some id := d.id? then
      arr := arr.push <| toJson id
    Json.arr arr

instance : FromJson ResolvableCompletionItemData where
  fromJson?
    | .arr elems => do
      if elems.size < 3 then
        .error "Expected array of size 3 in `FromJson` instance of `ResolvableCompletionItemData"
      let uri : DocumentUri ← fromJson? elems[0]!
      let line : Nat ← fromJson? elems[1]!
      let character : Nat ← fromJson? elems[2]!
      let mut cPos? : Option Nat := none
      let mut id? : Option CompletionIdentifier := none
      if let .ok (some cPos) := elems[3]?.mapM fromJson? then
        cPos? := some cPos
      if let .ok (some id) := elems[3]?.mapM fromJson? then
        id? := some id
      if let .ok (some cPos) := elems[4]?.mapM fromJson? then
        cPos? := some cPos
      if let .ok (some id) := elems[4]?.mapM fromJson? then
        id? := some id
      let pos := { line, character }
      return {
        uri
        pos
        cPos?
        id?
      }
    | _ => .error "Expected array in `FromJson` instance of `ResolvableCompletionItemData`"

structure ResolvableCompletionItem where
  label          : String
  detail?        : Option String := none
  documentation? : Option MarkupContent := none
  kind?          : Option CompletionItemKind := none
  textEdit?      : Option InsertReplaceEdit := none
  sortText?      : Option String := none
  data?          : Option ResolvableCompletionItemData := none
  tags?          : Option (Array CompletionItemTag) := none
  /-
  deprecated? : boolean
  preselect? : boolean
  filterText? : string
  insertText? : string
  insertTextFormat? : InsertTextFormat
  insertTextMode? : InsertTextMode
  additionalTextEdits? : TextEdit[]
  commitCharacters? : string[]
  command? : Command
  -/
  deriving FromJson, ToJson, Inhabited, BEq, Hashable

structure ResolvableCompletionList where
  isIncomplete : Bool
  items        : Array ResolvableCompletionItem
  deriving FromJson, ToJson

structure CompletionParams extends TextDocumentPositionParams where
  -- context? : CompletionContext
  deriving FromJson, ToJson

structure Hover where
  /- NOTE we should also accept MarkedString/MarkedString[] here
  but they are deprecated, so maybe can get away without. -/
  contents : MarkupContent
  range?   : Option Range := none
  deriving ToJson, FromJson

structure HoverParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

structure DeclarationParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

structure DefinitionParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

structure TypeDefinitionParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

structure ReferenceContext where
  includeDeclaration : Bool
  deriving FromJson, ToJson

structure ReferenceParams extends TextDocumentPositionParams where
  context : ReferenceContext
  deriving FromJson, ToJson

structure WorkspaceSymbolParams where
  query : String
  deriving FromJson, ToJson

structure DocumentHighlightParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

inductive DocumentHighlightKind where
  | text
  | read
  | write

instance : ToJson DocumentHighlightKind where
 toJson
   | DocumentHighlightKind.text => 1
   | DocumentHighlightKind.read => 2
   | DocumentHighlightKind.write => 3

structure DocumentHighlight where
  range : Range
  kind? : Option DocumentHighlightKind := none
  deriving ToJson

abbrev DocumentHighlightResult := Array DocumentHighlight

structure DocumentSymbolParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson

inductive SymbolKind where
  | file
  | module
  | namespace
  | package
  | class
  | method
  | property
  | field
  | constructor
  | enum
  | interface
  | function
  | variable
  | constant
  | string
  | number
  | boolean
  | array
  | object
  | key
  | null
  | enumMember
  | struct
  | event
  | operator
  | typeParameter
  deriving BEq, Hashable, Inhabited

instance : FromJson SymbolKind where
  fromJson?
    | 1  => .ok .file
    | 2  => .ok .module
    | 3  => .ok .namespace
    | 4  => .ok .package
    | 5  => .ok .class
    | 6  => .ok .method
    | 7  => .ok .property
    | 8  => .ok .field
    | 9  => .ok .constructor
    | 10 => .ok .enum
    | 11 => .ok .interface
    | 12 => .ok .function
    | 13 => .ok .variable
    | 14 => .ok .constant
    | 15 => .ok .string
    | 16 => .ok .number
    | 17 => .ok .boolean
    | 18 => .ok .array
    | 19 => .ok .object
    | 20 => .ok .key
    | 21 => .ok .null
    | 22 => .ok .enumMember
    | 23 => .ok .struct
    | 24 => .ok .event
    | 25 => .ok .operator
    | 26 => .ok .typeParameter
    | j  => .error s!"invalid symbol kind {j}"

instance : ToJson SymbolKind where
  toJson
    | .file          => 1
    | .module        => 2
    | .namespace     => 3
    | .package       => 4
    | .class         => 5
    | .method        => 6
    | .property      => 7
    | .field         => 8
    | .constructor   => 9
    | .enum          => 10
    | .interface     => 11
    | .function      => 12
    | .variable      => 13
    | .constant      => 14
    | .string        => 15
    | .number        => 16
    | .boolean       => 17
    | .array         => 18
    | .object        => 19
    | .key           => 20
    | .null          => 21
    | .enumMember    => 22
    | .struct        => 23
    | .event         => 24
    | .operator      => 25
    | .typeParameter => 26

structure DocumentSymbolAux (Self : Type) where
  name           : String
  detail?        : Option String := none
  kind           : SymbolKind
  -- tags? : Array SymbolTag
  range          : Range
  selectionRange : Range
  children?      : Option (Array Self) := none
  deriving FromJson, ToJson

inductive DocumentSymbol where
  | mk (sym : DocumentSymbolAux DocumentSymbol)

partial instance : ToJson DocumentSymbol where
  toJson :=
    let rec go
      | DocumentSymbol.mk sym =>
        have : ToJson DocumentSymbol := ⟨go⟩
        toJson sym
    go

structure DocumentSymbolResult where
  syms : Array DocumentSymbol

instance : ToJson DocumentSymbolResult where
  toJson dsr := toJson dsr.syms

inductive SymbolTag where
  | deprecated
  deriving BEq, Hashable, Inhabited

instance : FromJson SymbolTag where
  fromJson?
    | 1 => .ok .deprecated
    | j => .error s!"unknown symbol tag {j}"

instance : ToJson SymbolTag where
  toJson
    | .deprecated => 1

structure SymbolInformation where
  name           : String
  kind           : SymbolKind
  tags           : Array SymbolTag := #[]
  location       : Location
  containerName? : Option String := none
  deriving FromJson, ToJson

structure CallHierarchyPrepareParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

structure CallHierarchyItem where
  name           : String
  kind           : SymbolKind
  tags?          : Option (Array SymbolTag) := none
  detail?        : Option String := none
  uri            : DocumentUri
  range          : Range
  selectionRange : Range
  data?          : Option Json := none
  deriving FromJson, ToJson, BEq, Hashable, Inhabited

structure CallHierarchyIncomingCallsParams where
  item : CallHierarchyItem
  deriving FromJson, ToJson

structure CallHierarchyIncomingCall where
  «from»     : CallHierarchyItem
  fromRanges : Array Range
  deriving FromJson, ToJson, Inhabited

structure CallHierarchyOutgoingCallsParams where
  item : CallHierarchyItem
  deriving FromJson, ToJson

structure CallHierarchyOutgoingCall where
  to         : CallHierarchyItem
  fromRanges : Array Range
  deriving FromJson, ToJson, Inhabited

inductive SemanticTokenType where
  -- Used by Lean
  | keyword
  | variable
  | property
  | function
  /- Other types included by default in the LSP specification.
  Not used by the Lean core, but useful to users extending the Lean server. -/
  | namespace
  | type
  | class
  | enum
  | interface
  | struct
  | typeParameter
  | parameter
  | enumMember
  | event
  | method
  | macro
  | modifier
  | comment
  | string
  | number
  | regexp
  | operator
  | decorator
  -- Extensions
  | leanSorryLike
  deriving ToJson, FromJson, BEq, Hashable

-- must be in the same order as the constructors
def SemanticTokenType.names : Array String :=
  #["keyword", "variable", "property", "function", "namespace", "type", "class",
    "enum", "interface", "struct", "typeParameter", "parameter", "enumMember",
    "event", "method", "macro", "modifier", "comment", "string", "number",
    "regexp", "operator", "decorator", "leanSorryLike"]

def SemanticTokenType.toNat (tokenType : SemanticTokenType) : Nat :=
  tokenType.ctorIdx

-- sanity check
example {v : SemanticTokenType} : open SemanticTokenType in
    names[v.toNat]?.map (toString <| toJson ·) = some (toString <| toJson v) := by
  cases v <;> native_decide

/--
The semantic token modifiers included by default in the LSP specification.
Not used by the Lean core, but implementing them here allows them to be
utilized by users extending the Lean server.
-/
inductive SemanticTokenModifier where
  | declaration
  | definition
  | readonly
  | static
  | deprecated
  | abstract
  | async
  | modification
  | documentation
  | defaultLibrary
  deriving ToJson, FromJson

-- must be in the same order as the constructors
def SemanticTokenModifier.names : Array String :=
  #["declaration", "definition", "readonly", "static", "deprecated", "abstract",
    "async", "modification", "documentation", "defaultLibrary"]

def SemanticTokenModifier.toNat (modifier : SemanticTokenModifier) : Nat :=
  modifier.ctorIdx

-- sanity check
example {v : SemanticTokenModifier} : open SemanticTokenModifier in
    names[v.toNat]?.map (toString <| toJson ·) = some (toString <| toJson v) := by
  cases v <;> native_decide

structure SemanticTokensLegend where
  tokenTypes     : Array String
  tokenModifiers : Array String
  deriving FromJson, ToJson

structure SemanticTokensOptions where
  legend : SemanticTokensLegend
  range  : Bool
  full   : Bool /- | {
    delta?: boolean;
  } -/
  deriving FromJson, ToJson

structure SemanticTokensParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson

structure SemanticTokensRangeParams where
  textDocument : TextDocumentIdentifier
  range        : Range
  deriving FromJson, ToJson

structure SemanticTokens where
  resultId? : Option String := none
  data      : Array Nat
  deriving FromJson, ToJson

structure FoldingRangeParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson

inductive FoldingRangeKind where
  | comment
  | imports
  | region

instance : ToJson FoldingRangeKind where
  toJson
    | FoldingRangeKind.comment => "comment"
    | FoldingRangeKind.imports => "imports"
    | FoldingRangeKind.region  => "region"

structure FoldingRange where
  startLine : Nat
  endLine   : Nat
  kind?     : Option FoldingRangeKind := none
  deriving ToJson

structure RenameOptions where
  prepareProvider : Bool := false
  deriving FromJson, ToJson

structure RenameParams extends TextDocumentPositionParams where
  newName : String
  deriving FromJson, ToJson

structure PrepareRenameParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

structure InlayHintParams extends WorkDoneProgressParams where
  textDocument : TextDocumentIdentifier
  range        : Range
  deriving FromJson, ToJson

inductive InlayHintTooltip
  | plaintext (text : String)
  | markdown (markup : MarkupContent)

instance : FromJson InlayHintTooltip where
  fromJson?
    | .str s => .ok <| .plaintext s
    | j@(.obj _) => do return .markdown (← fromJson? j)
    | j => .error s!"invalid inlay hint tooltip {j}"

instance : ToJson InlayHintTooltip where
  toJson
    | .plaintext text => toJson text
    | .markdown markup => toJson markup

structure InlayHintLabelPart where
  value     : String
  tooltip?  : Option InlayHintTooltip := none
  location? : Option Location := none
  command?  : Option Command := none
  deriving FromJson, ToJson

inductive InlayHintLabel
  | name (n : String)
  | parts (p : Array InlayHintLabelPart)

instance : FromJson InlayHintLabel where
  fromJson?
    | .str s => .ok <| .name s
    | j@(.arr _) => do return .parts (← fromJson? j)
    | j => .error s!"invalid inlay hint label {j}"

instance : ToJson InlayHintLabel where
  toJson
    | .name n => toJson n
    | .parts p => toJson p

inductive InlayHintKind where
  | type
  | parameter

instance : FromJson InlayHintKind where
  fromJson?
    | 1 => .ok .type
    | 2 => .ok .parameter
    | j => .error s!"unknown inlay hint kind {j}"

instance : ToJson InlayHintKind where
  toJson
    | .type => 1
    | .parameter => 2

structure InlayHint where
  position      : Position
  label         : InlayHintLabel
  kind?         : Option InlayHintKind := none
  textEdits?    : Option (Array TextEdit) := none
  tooltip?      : Option (InlayHintTooltip) := none
  paddingLeft?  : Option Bool := none
  paddingRight? : Option Bool := none
  data?         : Option Json := none
  deriving FromJson, ToJson

structure InlayHintClientCapabilities where
  dynamicRegistration? : Option Bool := none
  resolveSupport?      : Option ResolveSupport := none
  deriving FromJson, ToJson

structure InlayHintOptions extends WorkDoneProgressOptions where
  resolveProvider? : Option Bool := none
  deriving FromJson, ToJson

inductive ParameterInformationLabel
  | name (name : String)
  | range (startUtf16Offset endUtf16Offset : Nat)

instance : FromJson ParameterInformationLabel where
  fromJson?
    | .str name => .ok <| .name name
    | .arr #[startUtf16OffsetJson, endUtf16OffsetJson] => do
      return .range (← fromJson? startUtf16OffsetJson) (← fromJson? endUtf16OffsetJson)
    | _ => .error "unexpected JSON for `ParameterInformationLabel`"

instance : ToJson ParameterInformationLabel where
  toJson
    | .name name => .str name
    | .range startUtf16Offset endUtf16Offset => .arr #[startUtf16Offset, endUtf16Offset]

structure ParameterInformation where
  label : ParameterInformationLabel
  documentation? : Option MarkupContent := none
  deriving FromJson, ToJson

structure SignatureInformation where
  label : String
  documentation? : Option MarkupContent := none
  parameters? : Option (Array ParameterInformation) := none
  activeParameter? : Option Nat := none
  deriving FromJson, ToJson

structure SignatureHelp where
  signatures : Array SignatureInformation
  activeSignature? : Option Nat := none
  activeParameter? : Option Nat := none
  deriving FromJson, ToJson

inductive SignatureHelpTriggerKind where
  | invoked
  | triggerCharacter
  | contentChange

instance : FromJson SignatureHelpTriggerKind where
  fromJson?
    | (1 : Nat) => .ok .invoked
    | (2 : Nat) => .ok .triggerCharacter
    | (3 : Nat) => .ok .contentChange
    | _ => .error "Unexpected JSON in `SignatureHelpTriggerKind`"

instance : ToJson SignatureHelpTriggerKind where
  toJson
    | .invoked => 1
    | .triggerCharacter => 2
    | .contentChange => 3

structure SignatureHelpContext where
  triggerKind : SignatureHelpTriggerKind
  triggerCharacter? : Option String := none
  isRetrigger : Bool
  activeSignatureHelp? : Option SignatureHelp := none
  deriving FromJson, ToJson

structure SignatureHelpParams extends TextDocumentPositionParams, WorkDoneProgressParams where
  context? : Option SignatureHelpContext := none
  deriving FromJson, ToJson

structure SignatureHelpOptions extends WorkDoneProgressOptions where
  triggerCharacters? : Option (Array String) := none
  retriggerCharacters? : Option (Array String) := none
  deriving FromJson, ToJson

structure DocumentColorParams extends WorkDoneProgressParams, PartialResultParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson

structure Color where
  red : Float
  green : Float
  blue : Float
  alpha : Float
  deriving FromJson, ToJson

structure ColorInformation where
  range : Range
  color : Color
  deriving FromJson, ToJson

structure DocumentColorOptions extends WorkDoneProgressOptions where
  deriving FromJson, ToJson

end Lsp
end Lean
