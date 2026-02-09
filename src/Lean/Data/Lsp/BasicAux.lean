/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Json.FromToJson.Basic

public section

/-
This module exists to cut the dependency on `Std.Data.TreeMap.AdditionalOperations` from a large
chunk of the meta framework.
-/

namespace Lean
namespace Lsp

open Json

abbrev DocumentUri := String

/-- We adopt the convention that zero-based UTF-16 positions as sent by LSP clients
are represented by `Lsp.Position` while internally we mostly use `String.Pos` UTF-8
offsets. For diagnostics, one-based `Lean.Position`s are used internally.
`character` is accepted liberally: actual character := min(line length, character) -/
structure Position where
  line : Nat
  character : Nat
  deriving Inhabited, BEq, Ord, Hashable, ToJson, FromJson, Repr

instance : ToString Position := ⟨fun p =>
  "(" ++ toString p.line ++ ", " ++ toString p.character ++ ")"⟩

instance : LT Position := ltOfOrd
instance : LE Position := leOfOrd

structure Range where
  start : Position
  «end» : Position
  deriving Inhabited, BEq, Hashable, ToJson, FromJson, Ord, Repr

instance : LT Range := ltOfOrd
instance : LE Range := leOfOrd

end Lsp
end Lean


