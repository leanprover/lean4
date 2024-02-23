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
