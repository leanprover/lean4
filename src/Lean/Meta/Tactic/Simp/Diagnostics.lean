/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Diagnostics
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

def mkSimpDiagSummary (counters : PHashMap Origin Nat) : MetaM DiagSummary := do
  let threshold := diagnostics.threshold.get (← getOptions)
  let entries := collectAboveThreshold counters threshold (fun _ => true) (lt := (· < ·))
  if entries.isEmpty then
    return {}
  else
    let mut data := #[]
    for (thmId, counter) in entries do
      let key ← match thmId with
        | .decl declName _ _ =>
          if (← getEnv).contains declName then
            pure m!"{MessageData.ofConst (← mkConstWithLevelParams declName)}"
          else
            pure m!"{declName} (builtin simproc)"
        | .fvar fvarId => pure m!"{mkFVar fvarId}"
        | _ => pure thmId.key
      data := data.push m!"{if data.isEmpty then "  " else "\n"}{key} ↦ {counter}"
    return { data, max := entries[0]!.2 }

def reportDiag (diag : Simp.Diagnostics) (diagOrig : Meta.Diagnostics) : MetaM Unit := do
  if (← isDiagnosticsEnabled) then
    let used ← mkSimpDiagSummary diag.usedThmCounter
    let tried ← mkSimpDiagSummary diag.triedThmCounter
    let unfoldCounter := subCounters (← get).diag.unfoldCounter diagOrig.unfoldCounter
    let unfoldDefault ← mkDiagSummaryForUnfolded unfoldCounter
    let unfoldInstance ← mkDiagSummaryForUnfolded unfoldCounter (instances := true)
    let unfoldReducible ← mkDiagSummaryForUnfoldedReducible unfoldCounter
    unless used.isEmpty && tried.isEmpty && unfoldDefault.isEmpty && unfoldInstance.isEmpty && unfoldReducible.isEmpty do
      let m := MessageData.nil
      let m := appendSection m `simp "used theorems" used
      let m := appendSection m `simp "tried theorems" tried
      let m := appendSection m `reduction "unfolded declarations" unfoldDefault
      let m := appendSection m `reduction "unfolded instances" unfoldInstance
      let m := appendSection m `reduction "unfolded reducible declarations" unfoldReducible
      let m := m ++ "use `set_option diagnostics.threshold <num>` to control threshold for reporting counters"
      logInfo m

end Lean.Meta.Simp
