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

structure Hover where
  /- NOTE we should also accept MarkedString/MarkedString[] here
  but they are deprecated, so maybe can get away without. -/
  contents : MarkupContent
  range? : Option Range := none
  deriving ToJson, FromJson

structure HoverParams extends TextDocumentPositionParams

instance : FromJson HoverParams := ⟨fun j => do
  let tdpp ← @fromJson? TextDocumentPositionParams _ j
  pure ⟨tdpp⟩⟩

instance : ToJson HoverParams :=
  ⟨fun o => toJson o.toTextDocumentPositionParams⟩


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
	| enum
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
        have ToJson DocumentSymbol := ⟨go⟩
        toJson sym
    go

structure DocumentSymbolResult where
  syms : Array DocumentSymbol

instance : ToJson DocumentSymbolResult where
  toJson dsr := toJson dsr.syms

end Lsp
end Lean
