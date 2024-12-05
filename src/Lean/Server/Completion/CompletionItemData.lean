/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Server.FileSource

namespace Lean.Lsp

/-- Used in `CompletionItem.data?`. -/
structure CompletionItemData where
  params : CompletionParams
  deriving FromJson, ToJson

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
def CompletionItem.getFileSource! (item : CompletionItem) : DocumentUri :=
  let r : Except String DocumentUri := do
    let some data := item.data?
      | throw s!"no data param on completion item {item.label}"
    let data : CompletionItemData ← fromJson? data
    return data.params.textDocument.uri
  match r with
  | Except.ok uri => uri
  | Except.error e => panic! e

instance : FileSource CompletionItem where
  fileSource := CompletionItem.getFileSource!

end Lean.Lsp
