/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Intro
import Lean.Util.ParamMinimizer
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.EMatchTheoremParam
import Lean.Meta.Tactic.Grind.EMatchTheoremPtr
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
generated `instantiate` tactic.

**Note**: We use a simple parameter optimizer for computing the `instantiate` tactic parameter.
We have a lower and upper bound for their parameters
The lower bound consists of the theorems actually used in the proof term, while the upper
bound includes all the theorems instantiated in a particular theorem instantiation step.
The lower bound is often sufficient to replay the proof, but in some cases, additional
theorems must be included because a theorem instantiation may contribute to the proof by
providing terms and many not be present in the final proof term.

**Note*: If an working `instantiate [...]` tactic cannot be produced, we produce the
tactic `instantiate approx` to indicate that this step is approximate and tweaking is needed.
We currently used unlimited budget for find the optimal parameter setting. We will add
a parameter to set the maximum number of iterations. After this implemented, we may generate
`instantiate only approx [...]` to indicate the parameter search has been interrupted and
a non-minimal set of parameters was used.
-/

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
  | false, true  => `(grind| instantiate only approx [$params,*])

def mkNewSeq (goal : Goal) (thms : Array EMatchTheorem) (seq : List TGrind) (approx : Bool) : GrindM (List TGrind) := do
  if thms.isEmpty && !approx then
    return seq
  else
    return ((← mkInstantiateTactic goal thms approx) :: seq)

abbrev EMatchTheoremIds := Std.HashMap EMatchTheoremPtr Nat

def getAllTheorems (map : EMatch.InstanceMap) : Array EMatchTheorem × EMatchTheoremIds := Id.run do
  let idAndThms := map.toArray
  -- **Note**: See note above. We want to sort here to reproduce the original instantiation order.
  let idAndThms := idAndThms.qsort fun (id₁, _) (id₂, _) => id₁.lt id₂
  let mut map := {}
  let mut thms := #[]
  for (_, thm) in idAndThms do
    unless map.contains { thm } do
      map  := map.insert { thm } thms.size
      thms := thms.push thm
  return (thms, map)

def mkMask (map : EMatchTheoremIds) (thms : Array EMatchTheorem) : CoreM (Array Bool) := do
  let mut result := Array.replicate map.size false
  for thm in thms do
    let some i := map.get? { thm } | throwError "`grind` internal error, theorem index not found"
    result := result.set! i true
  return result

def maskToThms (thms : Array EMatchTheorem) (mask : Array Bool) : Array EMatchTheorem := Id.run do
  let mut result := #[]
  for h : i in *...mask.size do
    if mask[i] then
      result := result.push thms[i]!
  return result

public def instantiate' : Action := fun goal kna kp => do
  let saved? ← saveStateIfTracing
  let ((progress, map), goal') ← GoalM.run goal ematch'
  if progress then
    match (← kp goal') with
    | .closed seq =>
      if (← getConfig).trace then
        let proof ← instantiateMVars (mkMVar goal.mvarId)
        let usedThms := collect proof map
        let (allThms, map) := getAllTheorems map
        -- We must have at least the ones used in the proof
        let initMask ← mkMask map usedThms
        let testMask (mask : Array Bool) : GrindM Bool := do
          checkSystem "`grind` `instantiate` tactic parameter optimizer"
          let thms := maskToThms allThms mask
          let newSeq ← mkNewSeq goal thms seq (approx := false)
          checkSeqAt saved? goal newSeq
        let r ← Util.ParamMinimizer.search initMask testMask
        let newSeq ← match r.status with
          | .missing => mkNewSeq goal #[] seq (approx := true)
          | .approx => mkNewSeq goal (maskToThms allThms r.paramMask) seq (approx := true)
          | .precise => mkNewSeq goal (maskToThms allThms r.paramMask) seq (approx := false)
        return .closed newSeq
      else
        return .closed []
    | r => return r
  else
    kna goal

public def instantiate : Action :=
  instantiate' >> assertAll

end Lean.Meta.Grind.Action
