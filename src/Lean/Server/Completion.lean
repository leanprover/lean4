/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
module

prelude
public import Lean.Server.Completion.CompletionCollectors
public import Std.Data.HashMap

public section

namespace Lean.Server.Completion
open Lsp
open Elab

private def filterDuplicateCompletionItems
    (items : Array ResolvableCompletionItem)
    : Array ResolvableCompletionItem := Id.run do
  let mut r : Array ResolvableCompletionItem := #[]
  let mut index : Std.HashSet (String × Option InsertReplaceEdit) := ∅
  for i in items do
    let key := (i.label, i.textEdit?)
    let (isDup, index') := index.containsThenInsert key
    index := index'
    if ! isDup then
      r := r.push i
  return r

partial def find?
    (mod      : Name)
    (pos      : Lsp.Position)
    (fileMap  : FileMap)
    (hoverPos : String.Pos.Raw)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    (caps     : ClientCapabilities)
    : CancellableM ResolvableCompletionList := do
  let (prioritizedPartitions, isComplete) := findPrioritizedCompletionPartitionsAt fileMap hoverPos cmdStx infoTree
  let mut allCompletions := #[]
  for partition in prioritizedPartitions do
    for (i, completionInfoPos) in partition do
      CancellableM.checkCancelled
      let completions ←
        match i.info with
        | .id stx id danglingDot lctx .. =>
          idCompletion mod pos completionInfoPos i.ctx lctx stx id i.hoverInfo danglingDot
        | .dot info .. =>
          dotCompletion mod pos completionInfoPos i.ctx info
        | .dotId _ id lctx expectedType? =>
          dotIdCompletion mod pos completionInfoPos i.ctx lctx id expectedType?
        | .fieldId _ id lctx structName =>
          fieldIdCompletion mod pos completionInfoPos i.ctx lctx id structName
        | .option stx =>
          optionCompletion mod pos completionInfoPos i.ctx stx caps
        | .errorName _ partialId =>
          errorNameCompletion mod pos completionInfoPos i.ctx partialId caps
        | .endSection _ id? danglingDot scopeNames =>
          endSectionCompletion mod pos completionInfoPos id? danglingDot scopeNames
        | .tactic .. =>
          tacticCompletion mod pos completionInfoPos i.ctx
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
