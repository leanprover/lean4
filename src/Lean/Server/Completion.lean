/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
prelude
import Lean.Server.Completion.CompletionCollectors

namespace Lean.Server.Completion
open Lsp
open Elab

private def filterDuplicateCompletionItems
    (items : Array ScoredCompletionItem)
    : Array ScoredCompletionItem :=
  let duplicationGroups := items.groupByKey fun s => (
      s.item.label,
      s.item.textEdit?,
      s.item.detail?,
      s.item.kind?,
      s.item.tags?,
      s.item.documentation?,
    )
  duplicationGroups.map (fun _ duplicateItems => duplicateItems.getMax? (·.score < ·.score) |>.get!)
    |>.valuesArray

/--
Sorts `items` descendingly according to their score and ascendingly according to their label
for equal scores.
-/
private def sortCompletionItems (items : Array ScoredCompletionItem) : Array CompletionItem :=
  let items := items.qsort fun ⟨i1, s1⟩ ⟨i2, s2⟩ =>
    if s1 != s2 then
      s1 > s2
    else
      i1.label.map (·.toLower) < i2.label.map (·.toLower)
  items.map (·.1)

/--
Assigns the `CompletionItem.sortText?` for all items in `completions` according to their order
in `completions`. This is necessary because clients will use their own sort order if the server
does not set it.
-/
private def assignSortTexts (completions : Array CompletionItem) : Array CompletionItem := Id.run do
  if completions.isEmpty then
    return #[]
  let items := completions.mapIdx fun i item =>
    { item with sortText? := toString i }
  let maxDigits := items[items.size - 1]!.sortText?.get!.length
  let items := items.map fun item =>
    let sortText := item.sortText?.get!
    let pad := List.replicate (maxDigits - sortText.length) '0' |>.asString
    { item with sortText? := pad ++ sortText }
  items

partial def find?
    (params   : CompletionParams)
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    (caps     : ClientCapabilities)
    : IO CompletionList := do
  let prioritizedPartitions := findPrioritizedCompletionPartitionsAt fileMap hoverPos cmdStx infoTree
  let mut allCompletions := #[]
  for partition in prioritizedPartitions do
    for (i, completionInfoPos) in partition do
      let completions : Array ScoredCompletionItem ←
        match i.info with
        | .id stx id danglingDot lctx .. =>
          idCompletion params completionInfoPos i.ctx lctx stx id i.hoverInfo danglingDot
        | .dot info .. =>
          dotCompletion params completionInfoPos i.ctx info
        | .dotId _ id lctx expectedType? =>
          dotIdCompletion params completionInfoPos i.ctx lctx id expectedType?
        | .fieldId _ id lctx structName =>
          fieldIdCompletion params completionInfoPos i.ctx lctx id structName
        | .option stx =>
          optionCompletion params completionInfoPos i.ctx stx caps
        | .tactic .. =>
          tacticCompletion params completionInfoPos i.ctx
        | _ =>
          pure #[]
      allCompletions := allCompletions ++ completions
    if ! allCompletions.isEmpty then
      -- Stop accumulating completions with lower priority if we found completions for a higher
      -- priority.
      break

  let finalCompletions := allCompletions
    |> filterDuplicateCompletionItems
    |> sortCompletionItems
    |> assignSortTexts
  return { items := finalCompletions, isIncomplete := true }

end Lean.Server.Completion
