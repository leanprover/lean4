/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/

import Lean.Message
import Lean.Parser.Types

namespace Lean.Language

/--
  The base class of all snapshots: all the generic information the language server
  needs about a snapshot. -/
structure Snapshot where
  /--
    The messages produced by this step. The union of message logs of all
    finished snapshots is reported to the user. -/
  msgLog : MessageLog
  /-- General elaboration metadata produced by this step. -/
  infoTree? : Option Elab.InfoTree := none
  -- (`InfoTree` is quite Lean-specific at this point, but we want to make it more generic)
deriving Inhabited

/-- A task producing some snapshot type (usually a subclass of `Snapshot`). -/
-- Longer-term TODO: Give the server more control over the priority of tasks,
-- depending on e.g. the cursor position. This may require starting the tasks
-- suspended (e.g. in `Thunk`). The server may also need more dependency
-- information for this in order to avoid priority inversion.
structure SnapshotTask (α : Type) where
  /-- Range that is marked as being processed by the server while the task is running. -/
  range : String.Range
  task : Task α
deriving Nonempty

def SnapshotTask.ofIO (range : String.Range) (act : BaseIO α) : BaseIO (SnapshotTask α) := do
  return {
    range
    task := (← BaseIO.asTask act)
  }

def SnapshotTask.pure (a : α) : SnapshotTask α where
  -- irrelevant when already finished
  range := default
  task := .pure a

def SnapshotTask.cancel (t : SnapshotTask α) : BaseIO Unit :=
  IO.cancel t.task

def SnapshotTask.map (t : SnapshotTask α) (f : α → β) : SnapshotTask β :=
  { t with task := t.task.map f }

/--
  Chain two snapshot tasks. The range is taken from the first task if not specified;
  the range of the second task is discarded. -/
def SnapshotTask.bindIO (t : SnapshotTask α) (act : α → BaseIO (SnapshotTask β)) (range : String.Range := t.range) :
    BaseIO (SnapshotTask β) :=
  return { range, task := (← BaseIO.bindTask t.task fun a => (·.task) <$> (act a)) }

def SnapshotTask.get (t : SnapshotTask α) : α :=
  t.task.get

/--
  Tree of snapshots where each snapshot comes with an array of asynchronous
  further subtrees. Used for asynchronously collecting information about the
  entirety of snapshots in the language server. The involved tasks may form a
  DAG on the `Task` dependency level but this is not captured by this data
  structure. -/
inductive SnapshotTree where
  | mk (element : Snapshot) (children : Array (SnapshotTask SnapshotTree))
deriving Nonempty
abbrev SnapshotTree.element : SnapshotTree → Snapshot
  | mk s _ => s
abbrev SnapshotTree.children : SnapshotTree → Array (SnapshotTask SnapshotTree)
  | mk _ children => children

/--
  Helper class for projecting a heterogeneous hierarchy of snapshot classes to a
  homogeneous representation. -/
class ToSnapshotTree (α : Type) where
  toSnapshotTree : α → SnapshotTree
export ToSnapshotTree (toSnapshotTree)

register_builtin_option printMessageEndPos : Bool := {
  defValue := false, descr := "print end position of each message in addition to start position"
}

/--
  Runs a tree of snapshots to conclusion and incrementally report messages
  on stdout. Messages are reported in tree preorder. -/
partial def SnapshotTree.runAndReport (s : SnapshotTree) (opts : Options) : IO Unit := do
  s.element.msgLog.forM (·.toString (includeEndPos := printMessageEndPos.get opts) >>= IO.println)
  for t in s.children do
    t.get.runAndReport opts

/-- Waits on and returns all snapshots in the tree. -/
partial def SnapshotTree.getAll (s : SnapshotTree) : Array Snapshot :=
  go s |>.run #[] |>.2
where
  go s : StateM (Array Snapshot) Unit := do
    modify (·.push s.element)
    for t in s.children do
      go t.get

/-- Reports `IO` exceptions as single snapshot message. -/
def withFatalExceptions (ex : Snapshot → α) (act : IO α) : BaseIO α := do
  match (← act.toBaseIO) with
  | .error e => return ex {
    msgLog := MessageLog.empty.add { fileName := "TODO", pos := ⟨0, 0⟩, data := e.toString }
  }
  | .ok a => return a

def get? (t? : Option (SnapshotTask α)) : BaseIO (Option α) := do
  let some t := t? | return none
  return if (← IO.hasFinished t.task) then t.get else none

def getOrCancel (t? : Option (SnapshotTask α)) : BaseIO (Option α) := do
  let some t := t? | return none
  if (← IO.hasFinished t.task) then
    return t.get
  IO.cancel t.task
  return none

/--
  Checks whether reparsing `stx` in `newSource` should result in `stx` again.
  `stopPos` is the furthest position the parser has looked at for producing
  `stx`, which usually is the extent of the subsequent token (if any) plus one. -/
-- This is a fundamentally different approach from the "go up one snapshot from
-- the point of change" in the old implementation which was failing in edge
-- cases and is not generalizable to a DAG of snapshots.
def unchangedParse (stx : Syntax) (stopPos : String.Pos) (newSource : String) : Bool :=
  if let .original start .. := stx.getHeadInfo then
    let oldSubstr := { start with stopPos }
    oldSubstr == { oldSubstr with str := newSource }
  else false

/-- Metadata that does not change during the lifetime of the language processing process. -/
structure ProcessingContext where
  mainModuleName : Name
  opts : Options

structure Language where
  InitialSnapshot : Type
  [instToSnapshotTree : ToSnapshotTree InitialSnapshot]
  process : ProcessingContext → (old? : Option InitialSnapshot) → Parser.InputContext → BaseIO InitialSnapshot
  -- TODO: is this the right interface for other languages as well?
  /-- Gets final environment, if any, that is to be used for persisting, code generation, etc. -/
  getFinalEnv? : InitialSnapshot → Option Environment

instance (lang : Language) : ToSnapshotTree lang.InitialSnapshot := lang.instToSnapshotTree

/-- Returns a function for processing a language using incremental snapshots. -/
partial def Language.mkIncrementalProcessor (lang : Language) :
    ProcessingContext → BaseIO (Parser.InputContext → BaseIO SnapshotTree) := fun ctx => do
  let oldRef ← IO.mkRef none
  return fun doc => do
    let snap ← lang.process ctx (← oldRef.get) doc
    oldRef.set (some snap)
    return toSnapshotTree snap
