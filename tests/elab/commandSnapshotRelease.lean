module
public meta import Lean
public meta import Lean.Server.Test.Cancel

/-!
Check that rechecking a changed command releases the old command-snapshot suffix before the new
elaboration finishes. An unresolved promise in the old suffix acts as a lifetime marker: its
result task becomes ready when the last reference to the promise is dropped.
-/

meta section

open Lean Elab Command Language Language.Lean Server.Test.Cancel

structure LifetimeMarker where
  promise : IO.Promise Unit
  deriving TypeName

elab "waitForSnapshotRelease" : command => do
  resolveSyncPromise "snapshot-release-entered"
  IO.wait (← getSyncPromise "snapshot-release-resume").result!

private def mkSnapshot (state : Command.State) : CommandParsedSnapshot := {
  diagnostics := .empty
  stx := .missing
  parserState := {}
  elabSnap := {
    diagnostics := .empty
    elabSnap := default
    resultSnap := .finished none { diagnostics := .empty, cmdState := state }
    infoTreeSnap := .finished none { diagnostics := .empty }
    reportSnap := default
  }
  nextCmdSnap? := none
}

-- Return before checking the marker so this stack frame cannot retain the old snapshots.
private def startRecheck (env : Environment) :
    IO (Task CommandParsedSnapshot × Task (Option Unit)) := do
  let marker ← IO.Promise.new
  let released := marker.result?
  let state := Command.mkState env
  let diagnostics ← Snapshot.Diagnostics.ofMessageLog {}
  let some ref := diagnostics.interactiveDiagsRef?
    | throw <| IO.userError "missing diagnostic cache for the lifetime marker"
  ref.set (some (.mk (LifetimeMarker.mk marker)))
  let suffix := { mkSnapshot state with diagnostics }
  let old := { mkSnapshot state with nextCmdSnap? := some (.finished none suffix) }
  let input := Parser.mkInputContext "waitForSnapshotRelease" "<snapshot-release>"
  let task ← processCommands input {} state
    (some (Parser.mkInputContext "old" "<snapshot-release>", old))
  return (task, released)

private def checkRelease (env : Environment) : IO Unit := do
  let entered ← getSyncPromise "snapshot-release-entered"
  let resume ← getSyncPromise "snapshot-release-resume"
  let (task, released) ← startRecheck env
  let tree := toSnapshotTree (← IO.wait task)
  let finished ← tree.waitAll
  try
    let reachedPause ← IO.waitAny
      [entered.result?.map (fun _ => true), finished.map (fun _ => false)] (by simp)
    unless reachedPause do
      throw <| IO.userError "rechecking finished without reaching the test command"
    unless ← IO.hasFinished released do
      throw <| IO.userError "old command-snapshot suffix is still retained during rechecking"
  finally
    resume.resolve ()
    IO.wait finished
  tree.forM fun snapshot => do
    if snapshot.diagnostics.msgLog.hasErrors then
      throw <| IO.userError "unexpected error while rechecking the test command"

run_cmd checkRelease (← getEnv)
