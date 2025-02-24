/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
prelude
import Lean.Server.Completion.CompletionCollectors
import Lean.Server.RequestCancellation
import Std.Data.HashMap

namespace Lean.Server.Completion
open Lsp
open Elab

private def filterDuplicateCompletionItems
    (items : Array CompletionItem)
    : Array CompletionItem :=
  let duplicationGroups := items.groupByKey fun i => (
      i.label,
      i.textEdit?,
      i.detail?,
      i.kind?,
      i.tags?,
      i.documentation?,
    )
  duplicationGroups.map (fun _ duplicateItems => duplicateItems[0]!)
    |>.valuesArray

partial def find?
    (params   : CompletionParams)
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    (caps     : ClientCapabilities)
    : CancellableM CompletionList := do
  let (prioritizedPartitions, isComplete) := findPrioritizedCompletionPartitionsAt fileMap hoverPos cmdStx infoTree
  let mut allCompletions := #[]
  for partition in prioritizedPartitions do
    for (i, completionInfoPos) in partition do
      CancellableM.checkCancelled
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
  return { items := finalCompletions, isIncomplete := ! isComplete }

end Lean.Server.Completion
