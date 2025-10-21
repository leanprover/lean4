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
import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
namespace Lean.Meta.Grind.Action

structure CollectState where
  visited       : Std.HashSet ExprPtr := {}
  collectedThms : Std.HashSet (Origin × EMatchTheoremKind) := {}
  thms          : Array EMatchTheorem := #[]

def collect (e : Expr) (map : EMatch.InstanceMap) : Array EMatchTheorem :=
  let (_, s) := go e |>.run {}
  s.thms
where
  go (e : Expr) : StateM CollectState Unit := do
    if isMarkedSubsingletonApp e then
      /-
      **Note**: We can ignore nested proofs and decidable instances.
      They are not part of current `grind` proof.
      -/
      return ()
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

inductive Param where
  | funDecl (declName : Name)
  | globalThm (declName : Name) (kind : EMatchTheoremKind) (minIndexable : Bool)
  | localThm (anchor : UInt64)

def Param.lt (p₁ p₂ : Param) : Bool :=
  if p₁.ctorIdx = p₂.ctorIdx then
    match p₁, p₂ with
    | .localThm a₁, .localThm a₂ => a₁ < a₂
    | .funDecl f₁, .funDecl f₂ => f₁.lt f₂
    | .globalThm n₁ k₁ m₁, .globalThm n₂ k₂ m₂ =>
      if n₁ != n₂ then n₁.lt n₂
      else if k₁ != k₂ then k₁.lt k₂
      else m₁ < m₂
    | _, _ => false
  else
    p₁.ctorIdx < p₂.ctorIdx

/--
Creates an `instantiate` tactic that takes the `usedThms` as parameters.
-/
def mkInstantiateTactic (goal : Goal) (usedThms : Array EMatchTheorem) (approx : Bool) : GrindM TGrind := goal.withContext do
  let numDigits ← getNumDigitsForLocalTheoremAnchors goal
  let mut params : Array Param := #[]
  let mut foundFns : NameSet := {}
  let mut foundLocals : Std.HashSet Grind.Origin := {}
  for thm in usedThms do
    unless (← isMatchEqLikeDeclName thm.origin.key) do
      match thm.origin with
      | .decl declName =>
        if let some fnName ← isEqnThm? declName then
          unless foundFns.contains fnName do
            foundFns := foundFns.insert fnName
            params := params.push <| .funDecl fnName
        else
          params := params.push <| .globalThm declName thm.kind thm.minIndexable
      | _ => unless foundLocals.contains thm.origin do
        foundLocals := foundLocals.insert thm.origin
        let anchor ← getAnchor (← inferType thm.proof)
        params := params.push <| .localThm anchor
  params := params.qsort Param.lt
  let paramStxs ← params.mapM fun param => do
    match param with
    | .funDecl declName =>
      let decl : Ident := mkIdent (← unresolveNameGlobalAvoidingLocals declName)
      `(Parser.Tactic.Grind.thm| $decl:ident)
    | .globalThm declName kind minIndexable => Grind.globalDeclToInstantiateParamSyntax declName kind minIndexable
    | .localThm anchor => `(Parser.Tactic.Grind.thm| $(← mkAnchorSyntax numDigits anchor):anchor)
  match paramStxs.isEmpty, approx with
  | true,  false => `(grind| instantiate only)
  | false, false => `(grind| instantiate only [$paramStxs,*])
  | true,  true  => `(grind| instantiate approx)
  | false, true  => `(grind| instantiate approx [$paramStxs,*])

def mkNewSeq (goal : Goal) (thms : Array EMatchTheorem) (seq : List TGrind) (approx : Bool) : GrindM (List TGrind) := do
  if thms.isEmpty then
    return seq
  else
    return ((← mkInstantiateTactic goal thms approx) :: seq)

def getAllTheorems (map : EMatch.InstanceMap) : Array EMatchTheorem :=
  map.toArray.map (·.2)

public def instantiate' : Action := fun goal kna kp => do
  let saved? ← saveStateIfTracing
  let ((progress, map), goal') ← GoalM.run goal ematch'
  if progress then
    match (← kp goal') with
    | .closed seq =>
      if (← getConfig).trace then
        let proof ← instantiateMVars (mkMVar goal.mvarId)
        let usedThms := collect proof map
        let newSeq ← mkNewSeq goal usedThms seq (approx := false)
        if (← checkSeqAt saved? goal newSeq) then
          return .closed newSeq
        else
          let allThms := getAllTheorems map
          let newSeq ← mkNewSeq goal allThms seq (approx := true)
          return .closed newSeq
      else
        return .closed []
    | r => return r
  else
    kna goal

public def instantiate : Action :=
  instantiate' >> assertAll

end Lean.Meta.Grind.Action
