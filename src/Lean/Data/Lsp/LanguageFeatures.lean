/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Data.Json
import Lean.Data.Lsp.Basic

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
  deriving Inhabited, DecidableEq, Repr

instance : ToJson CompletionItemKind where
  toJson a := toJson (a.toCtorIdx + 1)

instance : FromJson CompletionItemKind where
  fromJson? v := do
    let i : Nat ← fromJson? v
    return CompletionItemKind.ofNat (i-1)

structure InsertReplaceEdit where
  newText : String
  insert : Range
  replace : Range
  deriving FromJson, ToJson

structure CompletionItem where
  label : String
  detail? : Option String := none
  documentation? : Option MarkupContent := none
  kind? : Option CompletionItemKind := none
  textEdit? : Option InsertReplaceEdit := none
  /-
  tags? : CompletionItemTag[]
  deprecated? : boolean
  preselect? : boolean
  sortText? : string
  filterText? : string
  insertText? : string
  insertTextFormat? : InsertTextFormat
  insertTextMode? : InsertTextMode
  additionalTextEdits? : TextEdit[]
  commitCharacters? : string[]
  command? : Command
  data? : any -/
  deriving FromJson, ToJson, Inhabited

structure CompletionList where
  isIncomplete : Bool
  items : Array CompletionItem
  deriving FromJson, ToJson

structure CompletionParams extends TextDocumentPositionParams where
  -- context? : CompletionContext
  deriving FromJson, ToJson

structure Hover where
  /- NOTE we should also accept MarkedString/MarkedString[] here
  but they are deprecated, so maybe can get away without. -/
  contents : MarkupContent
  range? : Option Range := none
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

instance : ToJson SymbolKind where
 toJson
   | SymbolKind.file => 1
   | SymbolKind.module => 2
   | SymbolKind.namespace => 3
   | SymbolKind.package => 4
   | SymbolKind.class => 5
   | SymbolKind.method => 6
   | SymbolKind.property => 7
   | SymbolKind.field => 8
   | SymbolKind.constructor => 9
   | SymbolKind.enum => 10
   | SymbolKind.interface => 11
   | SymbolKind.function => 12
   | SymbolKind.variable => 13
   | SymbolKind.constant => 14
   | SymbolKind.string => 15
   | SymbolKind.number => 16
   | SymbolKind.boolean => 17
   | SymbolKind.array => 18
   | SymbolKind.object => 19
   | SymbolKind.key => 20
   | SymbolKind.null => 21
   | SymbolKind.enumMember => 22
   | SymbolKind.struct => 23
   | SymbolKind.event => 24
   | SymbolKind.operator => 25
   | SymbolKind.typeParameter => 26

structure DocumentSymbolAux (Self : Type) where
  name : String
  detail? : Option String := none
  kind : SymbolKind
  -- tags? : Array SymbolTag
  range : Range
  selectionRange : Range
  children? : Option (Array Self) := none
  deriving ToJson

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

instance : ToJson SymbolTag where
 toJson
   | SymbolTag.deprecated => 1

structure SymbolInformation where
  name : String
  kind : SymbolKind
  tags : Array SymbolTag := #[]
  location : Location
  containerName? : Option String := none
  deriving ToJson

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
  deriving ToJson, FromJson

-- must be in the same order as the constructors
def SemanticTokenType.names : Array String :=
  #["keyword", "variable", "property", "function", "namespace", "type", "class",
    "enum", "interface", "struct", "typeParameter", "parameter", "enumMember",
    "event", "method", "macro", "modifier", "comment", "string", "number",
    "regexp", "operator", "decorator", "leanSorryLike"]

def SemanticTokenType.toNat (type : SemanticTokenType) : Nat :=
  type.toCtorIdx

-- sanity check
-- TODO: restore after update-stage0
--example {v : SemanticTokenType} : open SemanticTokenType in
--    names[v.toNat]?.map (toString <| toJson ·) = some (toString <| toJson v) := by
--  cases v <;> native_decide

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
  modifier.toCtorIdx

-- sanity check
example {v : SemanticTokenModifier} : open SemanticTokenModifier in
    names[v.toNat]?.map (toString <| toJson ·) = some (toString <| toJson v) := by
  cases v <;> native_decide

structure SemanticTokensLegend where
  tokenTypes : Array String
  tokenModifiers : Array String
  deriving FromJson, ToJson

structure SemanticTokensOptions where
  legend : SemanticTokensLegend
  range : Bool
  full : Bool /- | {
    delta?: boolean;
  } -/
  deriving FromJson, ToJson

structure SemanticTokensParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson

structure SemanticTokensRangeParams where
  textDocument : TextDocumentIdentifier
  range : Range
  deriving FromJson, ToJson

structure SemanticTokens where
  resultId? : Option String := none
  data : Array Nat
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
    | FoldingRangeKind.region => "region"

structure FoldingRange where
  startLine : Nat
  endLine : Nat
  kind? : Option FoldingRangeKind := none
  deriving ToJson

structure RenameOptions where
  prepareProvider : Bool := false
  deriving FromJson, ToJson

structure RenameParams extends TextDocumentPositionParams where
  newName : String
  deriving FromJson, ToJson

structure PrepareRenameParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

end Lsp
end Lean
