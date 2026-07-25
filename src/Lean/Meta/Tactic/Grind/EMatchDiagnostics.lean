/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types

/-!
This module implements analysis tools for e-matching instantiation graphs. They are used to provide
the user insights on potential issues with e-matching in a proof.
-/

namespace Lean.Meta.Grind

structure NodeInfo where
  children : Std.HashSet EMatchDiagNode
  lctx : LocalContext
  deriving Inhabited

structure InstGraph where
  info : Std.HashMap EMatchDiagNode NodeInfo := {}
  deriving Inhabited

namespace InstGraph

def registerNode (graph : InstGraph) (info : EMatchDiagInfo) : InstGraph :=
  { graph with info := graph.info.insert info.target { children := {}, lctx := info.lctx } }

def addEdge (graph : InstGraph) (src dst : EMatchDiagNode) : InstGraph :=
  { graph with
      info := graph.info.modify src fun info => { info with children := info.children.insert dst }
  }

def ofTrace (trace : Array EMatchDiagInfo) : InstGraph := Id.run do
  let mut graph := trace.foldl (init := {}) registerNode
  for entry in trace do
    for source in entry.sources do
      graph := graph.addEdge source entry.target
  return graph

end InstGraph

abbrev GraphM := ReaderT InstGraph MetaM

def mkBranchingMessages (cost : Std.HashMap EMatchDiagNode Float) : GraphM (Option MessageData) := do
  let limit := grind.ematch.diagnostics.branchThreshold.get (← getOptions)
  let arr := (← read).info.iter
    |>.filter (·.2.children.size ≥ limit)
    |>.toArray
    |>.qsort (fun lhs rhs => Prod.lexLt (rhs.2.children.size, cost[rhs.1]!) (lhs.2.children.size, cost[lhs.1]!))
  if arr.isEmpty then return none

  let mut msgs := #[]
  for (node, { children, lctx }) in arr do
    let childrenCount := children.size
    msgs := msgs.push <| ← withLCtx' lctx do
      let children ← children.toArray.mapM fun c => do
        withLCtx' (← read).info[c]!.lctx do
          addMessageContext <| .trace { cls := `thm } m!"{c.origin.pp}: {← inferType c.proof}" #[]
      let t := .trace { cls := `thm } m!"{node.origin.pp}: {← inferType node.proof} has {childrenCount} direct follow up instances" children
      addMessageContext t

  return some <| .trace { cls := `thm } "Excessively Branching Instances" msgs

def mkCostMessages (diag : Array EMatchDiagInfo) :
    GraphM (Option MessageData × Std.HashMap EMatchDiagNode Float):= do
  let acc := Std.HashMap.ofArray <| (← read).info.keysArray.map (·, 1.0)
  let costs := diag.foldr (init := acc) fun v acc => Id.run do
    let mut acc := acc
    let costV : Float := acc[v.target]!
    let numParents := v.sources.length.toFloat
    for parent in v.sources do
      acc := acc.modify parent (· + costV / numParents)
    return acc
  let limit := grind.ematch.diagnostics.costThreshold.get (← getOptions) |>.toFloat
  let nodes := (← read).info.iter
    |>.filter (costs[·.1]! ≥ limit)
    |>.toArray
    |>.qsort (costs[·.1]! > costs[·.1]!)
  if nodes.isEmpty then return (none, costs)

  let mut msgs := #[]
  for (node, info) in nodes do
    msgs := msgs.push <| ← withLCtx' info.lctx do
      addMessageContext <| .trace { cls := `thm } m!"{node.origin.pp} : {← inferType node.proof} ↦ {costs[node]!}" #[]
  let msg := .trace { cls := `thm } "High Cost Instances" msgs
  return (some msg, costs)

def countersWithOriginToMessageData (header : String) (cls : Name) (data : Array (Origin × Name × Nat)) : MetaM MessageData := do
  let data := data.qsort fun (_, n₁, c₁) (_, n₂, c₂) => if c₁ == c₂ then Name.lt n₁ n₂ else c₁ > c₂
  let data ← data.mapM fun (origin, name, counter) =>
    match origin with
    | .decl _ => return .trace { cls } m!"{.ofConstName name} ↦ {counter}" #[]
    | _ => return .trace { cls } m!"{name} ↦ {counter}" #[]
  return .trace { cls } header data

def counterMsgs (counters : Counters) : MetaM MessageData :=
  let counters := counters.thm.toArray.map fun (origin, c) => Id.run do
    match origin with
    | .fvar fvarId =>
      let some userName := counters.fvarUserNames.find? fvarId | unreachable!
      return (origin, userName, c)
    | .decl n => return (origin, n, c)
    | .local n => return (origin, n, c)
    | .stx n _ => return (origin, n, c)
  countersWithOriginToMessageData "Theorem Instance Count" `thm counters

public def mkEMatchDiagMessages (trace : PArray EMatchDiagInfo) (counters : Counters) :
    MetaM (Option MessageData) := do
  let mut msgs := #[]

  unless counters.thm.isEmpty do
    msgs := msgs.push (← counterMsgs counters)

  unless trace.isEmpty do
    let trace := trace.toArray
    let graph := InstGraph.ofTrace trace

    let (msg?, cost) ← ReaderT.run (mkCostMessages trace) graph
    if let some msg := msg? then msgs := msgs.push msg

    let msg? ← ReaderT.run (mkBranchingMessages cost) graph
    if let some msg := msg? then msgs := msgs.push msg

  if msgs.isEmpty then return none

  return some <| .trace { cls := `ematch } "E-matching Diagnostics" msgs

end Lean.Meta.Grind
