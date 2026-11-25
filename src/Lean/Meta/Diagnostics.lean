/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
import Lean.PrettyPrinter

public section

namespace Lean.Meta

def collectAboveThreshold [BEq α] [Hashable α] (counters : PHashMap α Nat) (threshold : Nat) (p : α → Bool) (lt : α → α → Bool) : Array (α × Nat) := Id.run do
  let mut r := #[]
  for (declName, counter) in counters do
    if counter > threshold then
    if p declName then
      r := r.push (declName, counter)
  return r.qsort fun (d₁, c₁) (d₂, c₂) => if c₁ == c₂ then lt d₁ d₂ else c₁ > c₂

def subCounters [BEq α] [Hashable α] (newCounters oldCounters : PHashMap α Nat) : PHashMap α Nat := Id.run do
  let mut result := {}
  for (a, counterNew) in newCounters do
    if let some counterOld := oldCounters.find? a then
      result := result.insert a (counterNew - counterOld)
    else
      result := result.insert a counterNew
  return result

structure DiagSummary where
  data  : Array MessageData := #[]
  max   : Nat := 0
  deriving Inhabited

def DiagSummary.isEmpty (s : DiagSummary) : Bool :=
  s.data.isEmpty

def mkDiagSummary (cls : Name) (counters : PHashMap Name Nat) (p : Name → Bool := fun _ => true) : MetaM DiagSummary := do
  -- unrestricted: diagnostics only
  let threshold := diagnostics.threshold.get (← getOptionsUnrestricted)
  let entries := collectAboveThreshold counters threshold p Name.lt
  if entries.isEmpty then
    return {}
  else
    let mut data := #[]
    for (declName, counter) in entries do
      data := data.push <| .trace { cls } m!"{.ofConst (← mkConstWithLevelParams declName)} ↦ {counter}" #[]
    return { data, max := entries[0]!.2 }

def mkDiagSummaryForUnfolded (counters : PHashMap Name Nat) (instances := false) : MetaM DiagSummary := do
  let env ← getEnv
  mkDiagSummary `reduction counters fun declName =>
    getReducibilityStatusCore env declName matches .semireducible
    && isInstanceCore env declName == instances

def mkDiagSummaryForUnfoldedReducible (counters : PHashMap Name Nat) : MetaM DiagSummary := do
  let env ← getEnv
  mkDiagSummary `reduction counters fun declName =>
    getReducibilityStatusCore env declName matches .reducible

def mkDiagSummaryForUsedInstances : MetaM DiagSummary := do
  mkDiagSummary `type_class (← get).diag.instanceCounter

def mkDiagSynthPendingFailure (failures : PHashMap Expr MessageData) : MetaM DiagSummary := do
  if failures.isEmpty then
    return {}
  else
    let mut data := #[]
    for (_, msg) in failures do
      data := data.push <| .trace { cls := `type_class } msg #[]
    return { data }

/--
We use below that this returns `m` unchanged if `s.isEmpty`
-/
def appendSection (m : Array MessageData) (cls : Name) (header : String) (s : DiagSummary) (resultSummary := true) : Array MessageData :=
  if s.isEmpty then
    m
  else
    let header := if resultSummary then s!"{header} (max: {s.max}, num: {s.data.size}):" else header
    m.push <| .trace { cls } header s.data

/--
Warns about assignments to instance metavariables that `isDefEq` rejected at least
`warn.repeatedInstanceRejections` times, and resets their counter. Such repetitions come from
`isDefEq` retrying failing comparisons that contain the same instance hole, which can make
elaboration slow or exhaust the heartbeats.
-/
def reportInstanceRejections : MetaM Unit := do
  let rs := (← get).diag.instRejections
  if rs.isEmpty then return
  modify fun s => { s with diag := { s.diag with instRejections := {} } }
  let hits := rs.toList.filterMap fun (_, n, msg?) => msg?.map (n, ·)
  if hits.isEmpty then return
  let hits := hits.toArray.qsort (fun a b => a.1 > b.1)
  let shown := hits.extract 0 3
  let body := shown.foldl (init := MessageData.nil) fun m (n, msg) =>
    m ++ m!"\n\n{n} times: " ++ msg
  let more := if hits.size > shown.size then m!"\n\n(and {hits.size - shown.size} more)" else .nil
  logWarning <| m!"`isDefEq` rejected the same instance assignment many times: the type of the value \
    does not agree with the type of the instance metavariable at `.instances` transparency, and \
    no synthesized instance of that type is defeq to the value:{body}{more}" ++
    .note m!"Repeated failing comparisons can make elaboration slow or exhaust the heartbeats. \
      Disable this warning with `set_option warn.repeatedInstanceRejections 0`."

/-- Logs diagnostics and resets the counters -/
def reportDiag : MetaM Unit := do
  reportInstanceRejections
  if (← isDiagnosticsEnabled) then
    -- Diagnostic output may reference private declarations (e.g. `_match_*`,
    -- `_sparseCasesOn_*`) that are not visible in exporting mode (issue #13581).
    withoutExporting do
    let unfoldCounter := (← get).diag.unfoldCounter
    let unfoldDefault ← mkDiagSummaryForUnfolded unfoldCounter
    let unfoldInstance ← mkDiagSummaryForUnfolded unfoldCounter (instances := true)
    let unfoldAxiom ← mkDiagSummary `reduction (← get).diag.unfoldAxiomCounter
    let unfoldReducible ← mkDiagSummaryForUnfoldedReducible unfoldCounter
    let heu ← mkDiagSummary `def_eq (← get).diag.heuristicCounter
    let inst ← mkDiagSummaryForUsedInstances
    let synthPending ← mkDiagSynthPendingFailure (← get).diag.synthPendingFailures
    let unfoldKernel ← mkDiagSummary `kernel (Kernel.getDiagnostics (← getEnv)).unfoldCounter
    let m := #[]
    let m := appendSection m `reduction "unfolded declarations" unfoldDefault
    let m := appendSection m `reduction "unfolded instances" unfoldInstance
    let m := appendSection m `reduction "unfolded reducible declarations" unfoldReducible
    let m := appendSection m `type_class "used instances" inst
    -- unrestricted: diagnostics only
    let m := appendSection m `type_class
              s!"max synth pending failures (maxSynthPendingDepth: {maxSynthPendingDepth.get (← getOptionsUnrestricted)}), use `set_option maxSynthPendingDepth <limit>`"
              synthPending (resultSummary := false)
    let m := appendSection m `def_eq "heuristic for solving `f a =?= f b`" heu
    let m := appendSection m `reduction "Axioms (possibly imported non-exposed defs) that were tried to be unfolded" unfoldAxiom
    let m := appendSection m `kernel "unfolded declarations" unfoldKernel
    unless m.isEmpty do
      let m := m.push "use `set_option diagnostics.threshold <num>` to control threshold for reporting counters"
      logInfo <| .trace { cls := `diag, collapsed := false } "Diagnostics" m
    -- Reset any reported diagnostics, so that `reportDiag` can be called again
    modify (fun s => { s with diag := {} })
    modifyEnv (Kernel.setDiagnostics · {})

end Lean.Meta
