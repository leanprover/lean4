/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
prelude
import Lean.Server.Completion.SyntheticCompletion

namespace Lean.Server.Completion
open Elab

private def filterDuplicateCompletionInfos
    (infos : Array ContextualizedCompletionInfo)
    : Array ContextualizedCompletionInfo := Id.run do
  -- We don't expect there to be too many duplicate completion infos,
  -- so it's fine if this is quadratic (we don't need to implement `Hashable` / `LT` this way).
  let mut deduplicatedInfos : Array ContextualizedCompletionInfo := #[]
  for i in infos do
    if deduplicatedInfos.any (fun di => eq di.info i.info) then
      continue
    deduplicatedInfos := deduplicatedInfos.push i
  deduplicatedInfos
where
  eq : CompletionInfo → CompletionInfo → Bool
    | .dot ti₁ .., .dot ti₂ .. =>
      ti₁.stx.eqWithInfo ti₂.stx && ti₁.expr == ti₂.expr
    | .id stx₁ id₁ .., .id stx₂ id₂ .. =>
      stx₁.eqWithInfo stx₂ && id₁ == id₂
    | .dotId stx₁ id₁ .., .id stx₂ id₂ .. =>
      stx₁.eqWithInfo stx₂ && id₁ == id₂
    | .fieldId stx₁ id₁? _ structName₁, .fieldId stx₂ id₂? _ structName₂ =>
      stx₁.eqWithInfo stx₂ && id₁? == id₂? && structName₁ == structName₂
    | .namespaceId stx₁, .namespaceId stx₂ =>
      stx₁.eqWithInfo stx₂
    | .option stx₁, .option stx₂ =>
      stx₁.eqWithInfo stx₂
    | .endSection stx₁ scopeNames₁, .endSection stx₂ scopeNames₂ =>
      stx₁.eqWithInfo stx₂ && scopeNames₁ == scopeNames₂
    | .tactic stx₁, .tactic stx₂ =>
      stx₁.eqWithInfo stx₂
    | _, _ =>
      false

def findCompletionInfosAt
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Array ContextualizedCompletionInfo := Id.run do
  let ⟨hoverLine, _⟩ := fileMap.toPosition hoverPos
  let mut completionInfoCandidates := infoTree.foldInfo (init := #[]) (go hoverLine)
  if completionInfoCandidates.isEmpty then
    completionInfoCandidates := findSyntheticCompletions fileMap hoverPos cmdStx infoTree
  return filterDuplicateCompletionInfos completionInfoCandidates
where
  go
      (hoverLine : Nat)
      (ctx       : ContextInfo)
      (info      : Info)
      (best     : Array ContextualizedCompletionInfo)
      : Array ContextualizedCompletionInfo := Id.run do
    let .ofCompletionInfo completionInfo := info
      | return best
    if ! info.occursInOrOnBoundary hoverPos then
      return best
    let headPos := info.pos?.get!
    let tailPos := info.tailPos?.get!
    let hoverInfo :=
      if hoverPos < tailPos then
        HoverInfo.inside (hoverPos - headPos).byteIdx
      else
        HoverInfo.after
    let ⟨headPosLine, _⟩ := fileMap.toPosition headPos
    let ⟨tailPosLine, _⟩ := fileMap.toPosition info.tailPos?.get!
    if headPosLine != hoverLine || headPosLine != tailPosLine then
      return best
    return best.push { hoverInfo, ctx, info := completionInfo }

private def computePrioritizedCompletionPartitions
    (items : Array (ContextualizedCompletionInfo × Nat))
    : Array (Array (ContextualizedCompletionInfo × Nat)) :=
  let partitions := items.groupByKey fun (i, _) =>
    let isId := i.info matches .id ..
    let size? := Info.ofCompletionInfo i.info |>.size?
    (isId, size?)
  -- Sort partitions so that non-id completions infos come before id completion infos and
  -- within those two groups, smaller sizes come before larger sizes.
  let partitionsByPriority := partitions.toArray.qsort
    fun ((isId₁, size₁?), _) ((isId₂, size₂?), _) =>
      match size₁?, size₂? with
      | some _, none   => true
      | none,   some _ => false
      | _, _ =>
        match isId₁, isId₂ with
        | false, true  => true
        | true,  false => false
        | _,     _     => Id.run do
          let some size₁ := size₁?
            | return false
          let some size₂ := size₂?
            | return false
          return size₁ < size₂
  partitionsByPriority.map (·.2)

def findPrioritizedCompletionPartitionsAt
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Array (Array (ContextualizedCompletionInfo × Nat)) :=
  findCompletionInfosAt fileMap hoverPos cmdStx infoTree
    |>.zipWithIndex
    |> computePrioritizedCompletionPartitions

end Lean.Server.Completion
