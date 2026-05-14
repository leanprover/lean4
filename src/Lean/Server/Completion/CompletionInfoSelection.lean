/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
module

prelude
public import Lean.Server.Completion.SyntheticCompletion

public section

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
    | .option stx₁ pre₁, .option stx₂ pre₂=>
      stx₁.eqWithInfo stx₂ && pre₁ == pre₂
    | .errorName stx₁ .., .errorName stx₂ .. =>
      stx₁.eqWithInfo stx₂
    | .endSection stx₁ .., .endSection stx₂ .. =>
      stx₁.eqWithInfo stx₂
    | .tactic stx₁, .tactic stx₂ =>
      stx₁.eqWithInfo stx₂
    | _, _ =>
      false

def findCompletionInfosAt
    (fileMap  : FileMap)
    (hoverPos : String.Pos.Raw)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Array ContextualizedCompletionInfo × Bool := Id.run do
  let ⟨hoverLine, _⟩ := fileMap.toPosition hoverPos
  let mut isComplete := true
  let mut completionInfoCandidates := infoTree.foldInfo (init := #[]) (go hoverLine)
  if completionInfoCandidates.isEmpty then
    completionInfoCandidates := findSyntheticCompletions fileMap hoverPos cmdStx infoTree
    isComplete := false
  return (filterDuplicateCompletionInfos completionInfoCandidates, isComplete)
where
  go
      (hoverLine : Nat)
      (ctx       : ContextInfo)
      (info      : Info)
      (best     : Array ContextualizedCompletionInfo)
      : Array ContextualizedCompletionInfo := Id.run do
    let .ofCompletionInfo completionInfo := info
      | return best
    if ! containsHoverPos completionInfo then
      return best
    let headPos := info.pos?.get!
    let tailPos := info.tailPos?.get!
    let hoverInfo :=
      if hoverPos < tailPos then
        HoverInfo.inside (headPos.byteDistance hoverPos)
      else
        HoverInfo.after
    let ⟨headPosLine, _⟩ := fileMap.toPosition headPos
    let ⟨tailPosLine, _⟩ := fileMap.toPosition info.tailPos?.get!
    if headPosLine != hoverLine || headPosLine != tailPosLine then
      return best
    return best.push { hoverInfo, ctx, info := completionInfo }
  containsHoverPos (i : CompletionInfo) : Bool := Id.run do
    if let .option stx _ := i then
      if stx[1].isMissing then
        let some range := stx.getRangeWithTrailing? (canonicalOnly := true)
          | return false
        return range.contains hoverPos (includeStop := false)
    if let .endSection stx none .. := i then
      let some range := stx.getRangeWithTrailing? (canonicalOnly := true)
        | return false
      return range.contains hoverPos (includeStop := false)
    return Info.ofCompletionInfo i |>.occursInOrOnBoundary hoverPos

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

/--
Finds all `CompletionInfo`s (both from the `InfoTree` and synthetic ones), prioritizes them,
arranges them in partitions of `CompletionInfo`s with the same priority and sorts these partitions
so that `CompletionInfo`s with the highest priority come first.
The returned `CompletionInfo`s are also tagged with their index in `findCompletionInfosAt` so that
when resolving a `CompletionItem`, we can reconstruct which `CompletionInfo` it was created from.

In general, the `InfoTree` may contain multiple different `CompletionInfo`s covering `hoverPos`,
and so we need to decide which of these `CompletionInfo`s we want to use to show completions to the
user. We choose priorities by the following rules:
- Synthetic completions have the lowest priority since they are only intended as a backup.
- Non-identifier completions have the highest priority since they tend to be much more helpful than
  identifier completions when available since there are typically way too many of the latter.
- Within the three groups [non-id completions, id completions, synthetic completions],
  `CompletionInfo`s with a smaller range are considered to be better.
-/
def findPrioritizedCompletionPartitionsAt
    (fileMap  : FileMap)
    (hoverPos : String.Pos.Raw)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Array (Array (ContextualizedCompletionInfo × Nat)) × Bool :=
  let (infos, isComplete) := findCompletionInfosAt fileMap hoverPos cmdStx infoTree
  let partitions := infos.zipIdx |> computePrioritizedCompletionPartitions
  (partitions, isComplete)

end Lean.Server.Completion
