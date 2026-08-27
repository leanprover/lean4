/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Additional snapshot functionality that needs further imports.

Authors: Sebastian Ullrich
-/

module

prelude
public import Lean.Elab.InfoTree
import Init.Data.Format.Macro

public section

namespace Lean.Language

/-- Produces trace of given snapshot tree, synchronously waiting on all children. -/
partial def SnapshotTree.trace (s : SnapshotTree) : CoreM Unit :=
  go .skip s
where go range? s := do
  let file ← getFileMap
  let mut desc := f!"{s.element.desc}"
  match range? with
  | .some range => desc := desc ++ f!"{file.toPosition range.start}-{file.toPosition range.stop} "
  | .inherit => desc := desc ++ "<range inherited> "
  | .skip => desc := desc ++ "<no range> "
  let msgs ← s.element.diagnostics.msgLog.toList.mapM (·.toString)
  desc := desc ++ .prefixJoin "\n• " msgs
  withTraceNode `Elab.snapshotTree (fun _ => pure desc) do
    s.children.toList.forM fun c => go c.reportingRange c.get
    if let some t := s.element.infoTree? then
      trace[Elab.info] (← t.format)
