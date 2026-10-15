module
public meta import Lean.Elab.Command
public meta import Lean.Server.Test.Cancel

/-!
Tests that the exported view of an asynchronously elaborated theorem, which is an axiom carrying
only the signature, is available without waiting for the theorem's proof.
-/

open Lean Elab Command
open Lean.Server.Test.Cancel

/--
Fails if the exported constant info of the given declaration is not available yet. Afterwards
unblocks the declaration's proof, which should be waiting via `wait_for_sync`.
-/
elab "#assert_exported_info_available " id:ident : command => do
  try
    let env := (← getEnv).setExporting true
    let some info := env.findAsync? id.getId
      | throwError "`{id.getId}` is not exported"
    unless (← IO.hasFinished info.constInfo) do
      throwError "exported constant info of `{id.getId}` is not available yet"
    let info := info.toConstantInfo
    unless info.isAxiom do
      throwError "`{id.getId}` should be exported as an axiom"
    logInfo m!"{info.name} : {info.type}"
  finally
    resolveSyncPromise id.getId.toString

public theorem blockedThm (n : Nat) : n = n := by
  wait_for_sync "blockedThm"
  rfl

/-- info: blockedThm : ∀ (n : Nat), n = n -/
#guard_msgs in
#assert_exported_info_available blockedThm
