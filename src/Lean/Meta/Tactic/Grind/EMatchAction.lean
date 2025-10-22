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

/-
**Note**: The unique IDs created to instantiate theorems have the form `<prefix>.<num>`,
where `<num>` corresponds to the instantiation order within a particular proof branch.
Thus, by sorting the collected theorems using their corresponding unique IDs,
we can construct an `instantiate` tactic that performs the instantiations using
the original order.

**Note**: It is unclear at this point whether this is a good strategy or not.
The order in which things are asserted affects the proof found by `grind`.
Thus, preserving the original order should intuitively help ensure that the generated
tactic script for the continuation still closes the goal when combined with the
generated `instantiate` tactic. However, it does not guarantee that the
script can be successfully replayed, since we are filtering out instantiations that do
not appear in the final proof term. Recall that a theorem instance may
contribute to the proof search even if it does not appear in the final proof term.
-/

structure CollectState where
  visited       : Std.HashSet ExprPtr := {}
  collectedThms : Std.HashSet (Origin × EMatchTheoremKind) := {}
  idAndThms     : Array (Name × EMatchTheorem) := #[]

def collect (e : Expr) (map : EMatch.InstanceMap) : Array (Name × EMatchTheorem) :=
  let (_, s) := go e |>.run {}
  s.idAndThms
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
          modify fun s => { s with collectedThms := s.collectedThms.insert key, idAndThms := s.idAndThms.push (uniqueId, thm) }
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
def mkInstantiateTactic (goal : Goal) (usedThms : Array EMatchTheorem) (approx : Bool) : GrindM TGrind := goal.withContext do
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
  match params.isEmpty, approx with
  | true,  false => `(grind| instantiate only)
  | false, false => `(grind| instantiate only [$params,*])
  | true,  true  => `(grind| instantiate approx)
  | false, true  => `(grind| instantiate approx [$params,*])

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
        let usedIdAndThms := collect proof map
        -- **Note**: See note above. We want to sort here to reproduce the original instantiation order.
        let usedIdAndThms := usedIdAndThms.qsort fun (id₁, _) (id₂, _) => id₁.lt id₂
        let usedThms := usedIdAndThms.map (·.2)
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
