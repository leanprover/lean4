/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Action
public import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.EMatchTheoremParam
namespace Lean.Meta.Grind.Action

structure CollectState where
  visited       : Std.HashSet ExprPtr := {}
  collectedThms : Std.HashSet (Origin × EMatchTheoremKind) := {}
  thms          : Array EMatchTheorem := #[]

def collect (e : Expr) (map : EMatch.InstanceProofMap) : Array EMatchTheorem :=
  let (_, s) := go e |>.run {}
  s.thms
where
  go (e : Expr) : StateM CollectState Unit := do
    if (← get).visited.contains { expr := e } then
      return ()
    modify fun s => { s with visited := s.visited.insert { expr := e } }
    if let some uniqueId := EMatch.isTheoremInstanceProof? e then
      if let some thm := map[uniqueId]? then
        let key := (thm.origin, thm.kind)
        unless (← get).collectedThms.contains key do
          modify fun s => { s with collectedThms := s.collectedThms.insert key, thms := s.thms.push thm }
    match e with
    | .lam _ d b _
    | .forallE _ d b _ => go d; go b
    | .proj _ _ b
    | .mdata _ b       => go b
    | .letE _ t v b _  => go t; go v; go b
    | .app f a         => go f; go a
    | _ => return ()

/--
Creates an `instantiate` tactic that takes the `usedThms` as parameters.
-/
def mkInstantiateTactic (goal : Goal) (usedThms : Array EMatchTheorem) : GrindM TGrind := goal.withContext do
  let numDigits ← getNumDigitsForLocalTheoremAnchors goal
  let mut params : Array (TSyntax ``Parser.Tactic.Grind.thm) := #[]
  let mut foundFns : NameSet := {}
  let mut foundLocals : Std.HashSet Grind.Origin := {}
  for thm in usedThms do
    unless (← isMatchEqLikeDeclName thm.origin.key) do
      match thm.origin with
      | .decl declName =>
        if let some fnName ← isEqnThm? declName then
          unless foundFns.contains fnName do
            foundFns := foundFns.insert fnName
            let param ← Grind.globalDeclToInstantiateParamSyntax declName thm.kind thm.minIndexable
            params := params.push param
        else
          let param ← Grind.globalDeclToInstantiateParamSyntax declName thm.kind thm.minIndexable
          params := params.push param
      | _ => unless foundLocals.contains thm.origin do
        foundLocals := foundLocals.insert thm.origin
        let anchor ← getAnchor (← inferType thm.proof)
        let param ← `(Parser.Tactic.Grind.thm| $(← mkAnchorSyntax numDigits anchor):anchor)
        params := params.push param
  if params.isEmpty then
    `(grind| instantiate only)
  else
    `(grind| instantiate only [$params,*])

public def instantiate' : Action := fun goal kna kp => do
  let s ← saveStateIfTracing
  let ((progress, map), goal') ← GoalM.run goal ematch'
  if progress then
    match (← kp goal') with
    | .closed seq =>
      if (← getConfig).trace then
        let proof ← instantiateMVars (mkMVar goal.mvarId)
        let usedThms := collect proof map
        let newSeq ← if usedThms.isEmpty then
          pure seq
        else
          pure ((← mkInstantiateTactic goal usedThms) :: seq)
        if (← checkSeqAt s goal newSeq) then
          return .closed newSeq
        else
          let tac ← `(grind| instantiate)
          return .closed (tac :: seq)
      else
        return .closed []
    | r => return r
  else
    kna goal

public def instantiate : Action :=
  instantiate' >> assertAll

end Lean.Meta.Grind.Action
