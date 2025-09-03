/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Server.FileSource

public section

namespace Lean.Lsp

/-- Used in `CompletionItem.data?`. -/
structure CompletionItemData where
  mod : Name
  pos : Position

instance : ToJson CompletionItemData where
  toJson d := Json.arr #[d.mod.toString, d.pos.line, d.pos.character]

instance : FromJson CompletionItemData where
  fromJson?
  | .arr elems => do
    if elems.size < 3 then
      .error "Expected array of size 3 in `FromJson` instance of `CompletionItemData"
    let mod : Name ← fromJson? elems[0]!
    let line : Nat ← fromJson? elems[1]!
    let character : Nat ← fromJson? elems[2]!
    let pos := { line, character }
    return { mod, pos }
  | _ => .error "Expected array in `FromJson` instance of `CompletionItemData`"

/--
Yields the file source of `item` by attempting to parse `item.data?` to `CompletionItemData` and
obtaining the original file source from its `params` fields. Panics if `item.data?` is not present
or cannot be parsed to `CompletionItemData`.
Used when `completionItem/resolve` requests pass the watchdog to decide which file worker to forward
the request to.
Since this function can panic and clients typically send `completionItem/resolve` requests for every
selected completion item, all completion items returned by the server in `textDocument/completion`
requests must have a `data?` field that can be parsed to `CompletionItemData`.
-/
def CompletionItem.getFileSource! (item : CompletionItem) : FileIdent :=
  let r : Except String FileIdent := do
    let some data := item.data?
      | throw s!"no data param on completion item {item.label}"
    let data : CompletionItemData ← fromJson? data
    return .mod data.mod
  match r with
  | Except.ok uri => uri
  | Except.error e => panic! e

instance : FileSource CompletionItem where
  fileSource := CompletionItem.getFileSource!

end Lean.Lsp
