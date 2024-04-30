/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.PrettyPrinter
import Lean.Meta.Basic
import Lean.Meta.Instances

namespace Lean.Meta

private def collectAboveThreshold (counters : PHashMap Name Nat) (threshold : Nat) (p : Name → Bool) : Array (Name × Nat) := Id.run do
  let mut r := #[]
  for (declName, counter) in counters do
    if counter > threshold then
    if p declName then
      r := r.push (declName, counter)
  return r.qsort fun (d₁, c₁) (d₂, c₂) => if c₁ == c₂ then d₁.lt d₂ else c₁ > c₂

private def mkMessageBodyFor? (counters : PHashMap Name Nat) (threshold : Nat) (p : Name → Bool := fun _ => true) : MetaM (Option MessageData) := do
  let entries := collectAboveThreshold counters threshold p
  if entries.isEmpty then
    return none
  else
    let mut m := MessageData.nil
    for (declName, counter) in entries do
      unless m matches .nil do
        m := m ++ "\n"
      m := m ++ m!"{MessageData.ofConst (← mkConstWithLevelParams declName)} ↦ {counter}"
    return some m

private def appendOptMessageData (m : MessageData) (header : String) (m? : Option MessageData) : MessageData :=
  if let some m' := m? then
    if m matches .nil then
      header ++ indentD m'
    else
      m ++ "\n" ++ header ++ indentD m'
  else
    m

def reportDiag : MetaM Unit := do
  if (← isDiagnosticsEnabled) then
    let threshold := diagnostics.threshold.get (← getOptions)
    let mut m := MessageData.nil
    let env ← getEnv
    let unfoldDefault? ← mkMessageBodyFor? (← get).diag.unfoldCounter threshold fun declName =>
      getReducibilityStatusCore env declName matches .semireducible
      && !isInstanceCore env declName
    let unfoldInstance? ← mkMessageBodyFor? (← get).diag.unfoldCounter threshold fun declName =>
      getReducibilityStatusCore env declName matches .semireducible
      && isInstanceCore env declName
    let unfoldReducible? ← mkMessageBodyFor? (← get).diag.unfoldCounter threshold fun declName =>
      getReducibilityStatusCore env declName matches .reducible
    let heu? ← mkMessageBodyFor? (← get).diag.heuristicCounter threshold
    let inst? ← mkMessageBodyFor? (← get).diag.instanceCounter threshold
    if unfoldDefault?.isSome || unfoldInstance?.isSome || unfoldReducible?.isSome || heu?.isSome || inst?.isSome then
      m := appendOptMessageData m "unfolded declarations:" unfoldDefault?
      m := appendOptMessageData m "unfolded instances:" unfoldInstance?
      m := appendOptMessageData m "unfolded reducible declarations:" unfoldReducible?
      m := appendOptMessageData m "used instances:" inst?
      m := appendOptMessageData m "`isDefEq` heuristic:" heu?
      m := m ++ "\nuse `set_option diagnostics.threshold <num>` to control threshold for reporting counters"
      logInfo m

end Lean.Meta
