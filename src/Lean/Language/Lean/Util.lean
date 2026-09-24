/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Implementation of the Lean language: parsing and processing of header and commands, incremental
recompilation

Authors: Sebastian Ullrich, Marc Huisinga
-/

module

prelude

public import Lean.Language.Lean.Types
import Lean.Elab.InfoTree.Util

/-- Checks whether `r` contains `hoverPos`, taking into account EOF according to `text`. -/
public def Lean.FileMap.rangeContainsHoverPos (text : Lean.FileMap) (r : Lean.Syntax.Range)
    (hoverPos : String.Pos.Raw) (includeStop := false) : Bool :=
  -- When `hoverPos` is at the very end of the file, it is *after* the last position in `text`.
  -- However, for `includeStop = false`, all ranges stop at the last position in `text`,
  -- which always excludes a `hoverPos` at the very end of the file.
  -- For the purposes of the language server, we generally assume that ranges that extend to
  -- the end of the file also include a `hoverPos` at the very end of the file.
  let isRangeAtEOF := r.stop == text.source.rawEndPos
  r.contains hoverPos (includeStop := includeStop || isRangeAtEOF)

public def Lean.FileMap.rangeOverlapsRequestedRange
    (text : Lean.FileMap)
    (documentRange : Lean.Syntax.Range)
    (requestedRange : Lean.Syntax.Range)
    (includeDocumentRangeStop := false)
    (includeRequestedRangeStop := false)
    : Bool :=
  let isDocumentRangeAtEOF := documentRange.stop == text.source.rawEndPos
  documentRange.overlaps requestedRange
    (includeFirstStop := includeDocumentRangeStop || isDocumentRangeAtEOF)
    (includeSecondStop := includeRequestedRangeStop)

public def Lean.FileMap.rangeIncludesRequestedRange
    (text : Lean.FileMap)
    (documentRange : Lean.Syntax.Range)
    (requestedRange : Lean.Syntax.Range)
    (includeDocumentRangeStop := false)
    (includeRequestedRangeStop := false)
    : Bool :=
  let isDocumentRangeAtEOF := documentRange.stop == text.source.rawEndPos
  documentRange.includes requestedRange
    (includeSuperStop := includeDocumentRangeStop || isDocumentRangeAtEOF)
    (includeSubStop := includeRequestedRangeStop)

namespace Lean.Language

public inductive SnapshotTree.foldSnaps.Control where
  | done
  | proceed (foldChildren : Bool)

public partial def SnapshotTree.foldSnaps (tree : SnapshotTree) (init : α)
    (f : SnapshotTask SnapshotTree → α → Task (α × foldSnaps.Control)) : Task α :=
  let t := traverseTree init tree
  t.map (sync := true) (·.1)
where
  traverseTree (acc : α) (tree : SnapshotTree) : Task (α × Bool) :=
    traverseChildren acc tree.children.toList

  traverseChildren (acc : α) : List (SnapshotTask SnapshotTree) → Task (α × Bool)
    | [] => .pure (acc, false)
    | child::otherChildren =>
      f child acc |>.bind (sync := true) fun (acc, control) => Id.run do
        let .proceed foldChildrenOfChild := control
          | return .pure (acc, true)
        if ! foldChildrenOfChild then
          return traverseChildren acc otherChildren
        let subtreeTask := child.task.bind (sync := true) fun tree =>
          traverseTree acc tree
        return subtreeTask.bind (sync := true) fun (acc, done) => Id.run do
          if done then
            return .pure (acc, done)
          return traverseChildren acc otherChildren

/--
Finds the first (in pre-order) snapshot task in `tree` that contains `hoverPos`
(including whitespace) and which contains an info tree, and then returns that info tree,
waiting for any snapshot tasks on the way.
Subtrees that do not contain the position are skipped without forcing their tasks.
If the caller of this function needs the correct snapshot when the cursor is on whitespace,
then this function is likely the wrong one to call, as it simply yields the first snapshot
that contains `hoverPos` in its whitespace, which is not necessarily the correct one
(e.g. it may be indentation-sensitive).
-/
public partial def SnapshotTree.findInfoTreeAtPos (text : FileMap) (tree : SnapshotTree)
    (hoverPos : String.Pos.Raw) (includeStop : Bool) : Task (Option Elab.InfoTree) :=
  tree.foldSnaps (init := none) fun snap _ => Id.run do
    let some stx := snap.stx?
      -- One of the invariants of the snapshot tree is that `stx? = none` implies that
      -- this entire subtree has no relevant `InfoTree` information, so we can safely discard it
      -- here.
      | return .pure (none, .proceed (foldChildren := false))
    let some range := stx.getRangeWithTrailing? (canonicalOnly := true)
      -- In the worst case, the `infoTreeSnap` of the `CommandParsedSnap` will have canonical
      -- syntax that we can use here, so ignoring snapshots with non-canonical syntax can only
      -- at worst break incrementality in request handlers.
      | return .pure (none, .proceed (foldChildren := true))
    if ! text.rangeContainsHoverPos range hoverPos includeStop then
      -- Subtrees of the snapshot tree always have syntax ranges that are contained in those of
      -- their parents, so we can terminate early here.
      return .pure (none, .proceed (foldChildren := false))
    return snap.task.map (sync := true) fun tree => Id.run do
      let some infoTree := tree.element.infoTree?
        | return (none, .proceed (foldChildren := true))
      return (infoTree, .done)

public partial def SnapshotTree.foldInfosInRange (tree : SnapshotTree) (requestedRange : Lean.Syntax.Range)
    (init : α) (f : Elab.ContextInfo → Elab.Info → α → α) : Task α :=
  tree.foldSnaps (init := init) fun snap acc => Id.run do
    let some stx := snap.stx?
      | return .pure (acc, .proceed (foldChildren := false))
    let some range := stx.getRangeWithTrailing? (canonicalOnly := true)
      | return .pure (acc, .proceed (foldChildren := true))
    if ! range.overlaps requestedRange (includeFirstStop := true) (includeSecondStop := true) then
      return .pure (acc, .proceed (foldChildren := false))
    return snap.task.map (sync := true) fun tree => Id.run do
      let some infoTree := tree.element.infoTree?
        | return (acc, .proceed (foldChildren := true))
      let acc := infoTree.foldInfo (init := acc) fun ctx i acc => Id.run do
        let some r := i.range?
          | return acc
        if ! r.overlaps requestedRange (includeFirstStop := true) (includeSecondStop := true) then
          return acc
        return f ctx i acc
      return (acc, .proceed (foldChildren := true))

public partial def SnapshotTree.collectMessagesInRange (tree : SnapshotTree)
    (requestedRange : Lean.Syntax.Range) : Task MessageLog :=
  tree.foldSnaps (init := .empty) fun snap log => Id.run do
    let some stx := snap.stx?
      | return .pure (log, .proceed (foldChildren := true))
    let some range := stx.getRangeWithTrailing? (canonicalOnly := true)
      | return .pure (log, .proceed (foldChildren := true))
    if ! range.overlaps requestedRange (includeFirstStop := true) (includeSecondStop := true) then
      return .pure (log, .proceed (foldChildren := false))
    return snap.task.map (sync := true) fun tree => Id.run do
      return (log ++ tree.element.diagnostics.msgLog, .proceed (foldChildren := true))

end Lean.Language

namespace Lean.Language.Lean

/-- Finds the first `CommandParsedSnapshot` containing `hoverPos`, asynchronously. -/
public partial def findCmdParsedSnap (initSnap : InitialSnapshot) (text : FileMap) (hoverPos : String.Pos.Raw)
    : Task (Option CommandParsedSnapshot) := Id.run do
  let some headerParsed := initSnap.result?
    | .pure none
  headerParsed.processedSnap.task.bind (sync := true) fun headerProcessed => Id.run do
    let some headerSuccess := headerProcessed.result?
      | return .pure none
    let firstCmdSnapTask : Task CommandParsedSnapshot := headerSuccess.firstCmdSnap.task
    firstCmdSnapTask.bind (sync := true) go
where
  go (cmdParsed : CommandParsedSnapshot) : Task (Option CommandParsedSnapshot) := Id.run do
    if containsHoverPos cmdParsed then
      return .pure (some cmdParsed)
    if isAfterHoverPos cmdParsed then
      -- This should never happen in principle
      -- (commands + trailing ws are consecutive and there is no unassigned space between them),
      -- but it's always good to eliminate one additional assumption.
      return .pure none
    match cmdParsed.nextCmdSnap? with
    | some next =>
      next.task.bind (sync := true) go
    | none => .pure none

  containsHoverPos (cmdParsed : CommandParsedSnapshot) : Bool := Id.run do
    let some range := cmdParsed.stx.getRangeWithTrailing? (canonicalOnly := true)
      | return false
    return text.rangeContainsHoverPos range hoverPos (includeStop := false)

  isAfterHoverPos (cmdParsed : CommandParsedSnapshot) : Bool := Id.run do
    let some startPos := cmdParsed.stx.getPos? (canonicalOnly := true)
      | return false
    return hoverPos < startPos

/--
Finds the command syntax and info tree of the first snapshot task containing `pos`, asynchronously.
The info tree may be from a nested snapshot, such as a single tactic.

See `SnapshotTree.findInfoTreeAtPos` for details on how the search is done.
-/
public def findCmdDataAtPos
    (initSnap : InitialSnapshot) (text : FileMap)
    (hoverPos : String.Pos.Raw)
    (includeStop : Bool)
    : Task (Option (Syntax × Elab.InfoTree)) :=
  findCmdParsedSnap initSnap text hoverPos |>.bind (sync := true) fun
    | some cmdParsed => toSnapshotTree cmdParsed.elabSnap |>.findInfoTreeAtPos text hoverPos includeStop |>.bind (sync := true) fun
      | some infoTree => .pure <| some (cmdParsed.stx, infoTree)
      | none          => cmdParsed.elabSnap.infoTreeSnap.task.map (sync := true) fun s =>
        assert! s.infoTree?.isSome
        some (cmdParsed.stx, s.infoTree?.get!)
    | none => .pure none
/--
Finds the info tree of the first snapshot task containing `pos`, asynchronously.
The info tree may be from a nested snapshot, such as a single tactic.

See `SnapshotTree.findInfoTreeAtPos` for details on how the search is done.
-/
public partial def findInfoTreeAtPos
    (initSnap : InitialSnapshot) (text : FileMap)
    (hoverPos : String.Pos.Raw)
    (includeStop : Bool)
    : Task (Option Elab.InfoTree) :=
  findCmdDataAtPos initSnap text hoverPos includeStop |>.map (sync := true) (·.map (·.2))

public structure HeaderData where
  stx : Syntax
  parserState? : Option Parser.ModuleParserState
  cmdState? : Option Elab.Command.State

public structure CommandData where
  stx : Syntax
  parserState : Parser.ModuleParserState
  cmdState : Elab.Command.State

public structure ModuleData where
  headerData : HeaderData
  cmdData : Array CommandData
  /--
  `true` iff the module header or any command produced parse errors. Note that error recovery
  in the parser may produce a structurally well-formed `Syntax` tree even when there were parse
  errors, so checking `Syntax.hasMissing` is not sufficient to detect them.
  -/
  hasParseErrors : Bool := false

/--
Collects the syntax, parser states and, if `collectCmdStates` is set, the elaboration states of the
header and all commands of the module described by `initSnap`.

Since collecting the elaboration state of a command means waiting for its elaboration to finish,
`collectCmdStates` should only be set when these states are actually needed. The elaboration state
of the header is always collected as it is available without waiting for any command elaboration.
-/
public partial def moduleData (initSnap : Language.Lean.InitialSnapshot)
    : Task ModuleData := Id.run do
  let headerStx := initSnap.stx
  let acc : ModuleData := {
    headerData := {
      stx := headerStx
      parserState? := none
      cmdState? := none
    }
    cmdData := #[]
  }
  let some headerParsedState := initSnap.result?
    | return .pure { acc with hasParseErrors := true }
  let acc := {
    acc with
    headerData := {
      acc.headerData with
      parserState? := some headerParsedState.parserState
    }
  }
  headerParsedState.processedSnap.task.bind (sync := true) fun headerProcessedSnap => Id.run do
    let some headerProcessedState := headerProcessedSnap.result?
      | return .pure acc
    let acc := {
      acc with
      headerData := {
        acc.headerData with
        cmdState? := some headerProcessedState.cmdState
      }
    }
    go headerProcessedState.firstCmdSnap acc
where
  go
      (cmdParsedSnapTask : Language.SnapshotTask Language.Lean.CommandParsedSnapshot)
      (acc : ModuleData) :
      Task ModuleData :=
    cmdParsedSnapTask.task.bind (sync := true) fun cmdParsedSnap =>
      cmdParsedSnap.elabSnap.resultSnap.task.bind (sync := true) fun cmdResultSnap => Id.run do

        let acc := {
          acc with
          cmdData := acc.cmdData.push {
            stx := cmdParsedSnap.stx
            parserState := cmdParsedSnap.parserState
            cmdState := cmdResultSnap.cmdState
          }
          hasParseErrors :=
            acc.hasParseErrors || cmdParsedSnap.diagnostics.msgLog.hasErrors
        }
        let some nextCmdParsedSnapTask := cmdParsedSnap.nextCmdSnap?
          | return .pure acc
        go nextCmdParsedSnapTask acc
