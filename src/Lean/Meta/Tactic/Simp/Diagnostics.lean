/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Diagnostics
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

private def originToKey (thmId : Origin) : MetaM MessageData := do
  match thmId with
  | .decl declName _ _ =>
    if (← getEnv).contains declName then
      pure m!"{.ofConstName declName}"
    else
      pure m!"{declName} (builtin simproc)"
  | .fvar fvarId => pure m!"{mkFVar fvarId}"
  | _ => pure thmId.key

def mkSimpDiagSummary (counters : PHashMap Origin Nat) (usedCounters? : Option (PHashMap Origin Nat) := none) : MetaM DiagSummary := do
  let threshold := diagnostics.threshold.get (← getOptions)
  let entries := collectAboveThreshold counters threshold (fun _ => true) (lt := (· < ·))
  if entries.isEmpty then
    return {}
  else
    let mut data := #[]
    for (thmId, counter) in entries do
      let key ← originToKey thmId
      let usedMsg ← if let some usedCounters := usedCounters? then
        if let some c := usedCounters.find? thmId then pure s!", succeeded: {c}" else pure s!" {crossEmoji}" -- not used
      else
        pure ""
      data := data.push <| .trace { cls := `simp } m!"{key} ↦ {counter}{usedMsg}" #[]
    return { data, max := entries[0]!.2 }

private def mkTheoremsWithBadKeySummary (thms : PArray SimpTheorem) : MetaM DiagSummary := do
  if thms.isEmpty then
    return {}
  else
    let mut data := #[]
    for thm in thms do
      data := data.push <| .trace { cls := `simp } m!"{← originToKey thm.origin}, key: {← DiscrTree.keysAsPattern thm.keys}" #[]
      pure ()
    return { data }

def reportDiag (diag : Simp.Diagnostics) : MetaM Unit := do
  if (← isDiagnosticsEnabled) then
    let used ← mkSimpDiagSummary diag.usedThmCounter
    let tried ← mkSimpDiagSummary diag.triedThmCounter diag.usedThmCounter
    let congr ← mkDiagSummary `simp diag.congrThmCounter
    let thmsWithBadKeys ← mkTheoremsWithBadKeySummary diag.thmsWithBadKeys
    unless used.isEmpty && tried.isEmpty && congr.isEmpty && thmsWithBadKeys.isEmpty do
      let m := MessageData.nil
      let m := appendSection m `simp "used theorems" used
      let m := appendSection m `simp "tried theorems" tried
      let m := appendSection m `simp "tried congruence theorems" congr
      let m := appendSection m `simp "theorems with bad keys" thmsWithBadKeys (resultSummary := false)
      let m := m ++ "use `set_option diagnostics.threshold <num>` to control threshold for reporting counters"
      logInfo m

end Lean.Meta.Simp
