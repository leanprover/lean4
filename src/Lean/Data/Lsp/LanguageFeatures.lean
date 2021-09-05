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

structure CompletionItem where
  label : String
  detail? : Option String
  documentation? : Option MarkupContent
  /-
  kind? : CompletionItemKind
  tags? : CompletionItemTag[]
  deprecated? : boolean
  preselect? : boolean
  sortText? : string
  filterText? : string
  insertText? : string
  insertTextFormat? : InsertTextFormat
  insertTextMode? : InsertTextMode
  textEdit? : TextEdit | InsertReplaceEdit
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
  | «namespace»
  | package
  | «class»
  | method
  | property
  | field
  | constructor
  | «enum»
  | interface
  | function
  | «variable»
  | «constant»
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

inductive SemanticTokenType where
  | keyword
  | «variable»
  | property
  /-
  | «namespace»
  | type
  | «class»
  | enum
  | interface
  | struct
  | typeParameter
  | parameter
  | enumMember
  | event
  | function
  | method
  | «macro»
  | modifier
  | comment
  | string
  | number
  | regexp
  | operator
  -/

def SemanticTokenType.names : Array String :=
  #["keyword", "variable", "property"]

-- must be the correct index in `names`
def SemanticTokenType.toNat : SemanticTokenType → Nat
  | keyword    => 0
  | «variable» => 1
  | property   => 2

/-
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
-/

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
  -- resultId?: string;
  data : Array Nat
  deriving FromJson, ToJson

end Lsp
end Lean
