/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.InstantiateS
namespace Lean.Meta.Sym
open Grind

/-!
This module implements efficient pattern matching and unification module for the symbolic simulation
framework (`Sym`). The design prioritizes performance by using a two-phase approach:

# Phase 1 (Syntactic Matching)
- Patterns use de Bruijn indices for expression variables and renamed level params (`_uvar.0`, `_uvar.1`, ...) for universe variables
- Matching is purely structural after reducible definitions are unfolded during preprocessing
- Universe levels treat `max` and `imax` as uninterpreted functions (no AC reasoning)
- Binders and term metavariables are deferred to Phase 2

# Phase 2 (Pending Constraints) [WIP]
- Handles binders (Miller patterns) and metavariable unification
- Converts remaining de Bruijn variables to metavariables
- Falls back to `isDefEq` when necessary

# Key design decisions:
- Preprocessing unfolds reducible definitions and performs beta/zeta reduction
- Kernel projections are expected to be folded as projection applications before matching
- Assignment conflicts are deferred to pending rather than invoking `isDefEq` inline
- `instantiateRevS` ensures maximal sharing of result expressions
-/

public structure Pattern where
  levelParams    : List Name
  varTypes       : Array Expr
  pattern        : Expr
  deriving Inhabited

def uvarPrefix : Name := `_uvar

def isUVar? (n : Name) : Option Nat := Id.run do
  let .num p idx := n | return none
  unless p == uvarPrefix do return none
  return some idx

def preprocessType (type : Expr) : MetaM Expr := do
  let type ← unfoldReducible type
  let type ← Core.betaReduce type
  zetaReduce type

public def mkPatternFromTheorem (declName : Name) : MetaM Pattern := do
  let info ← getConstInfo declName
  let levelParams := info.levelParams.mapIdx fun i _ => Name.num uvarPrefix i
  let us := levelParams.map mkLevelParam
  let type ← instantiateTypeLevelParams info.toConstantVal us
  let type ← preprocessType type
  -- **TODO**: save position of instance arguments
  let rec go (type : Expr) (varTypes : Array Expr) : Pattern :=
    match type with
    | .forallE _ d b _ => go b (varTypes.push d)
    | _ => { levelParams, varTypes, pattern := type }
  return go type #[]

structure UnifyM.Context where
  pattern : Pattern
  unify   : Bool := true

structure UnifyM.State where
  eAssignment  : Array (Option Expr)   := #[]
  uAssignment  : Array (Option Level)  := #[]
  ePending     : Array (Expr × Expr)   := #[]
  uPending     : Array (Level × Level) := #[]
  us           : List Level            := []
  args         : Array Expr            := #[]

abbrev UnifyM := ReaderT UnifyM.Context StateRefT UnifyM.State SymM

def pushPending (p : Expr) (e : Expr) : UnifyM Unit :=
  modify fun s => { s with ePending := s.ePending.push (p, e) }

def pushLevelPending (u : Level) (v : Level) : UnifyM Unit :=
  modify fun s => { s with uPending := s.uPending.push (u, v) }

def assignExpr (bidx : Nat) (e : Expr) : UnifyM Bool := do
  let s ← get
  let i := s.eAssignment.size - bidx - 1
  if let some e' := s.eAssignment[i]! then
    if isSameExpr e e' then return true
    else
      pushPending e' e
      return true
  else
    modify fun s => { s with eAssignment := s.eAssignment.set! i (some e) }
    return true

def assignLevel (uidx : Nat) (u : Level) : UnifyM Bool := do
  if let some u' := (← get).uAssignment[uidx]! then
    isLevelDefEq u u'
  else
    modify fun s => { s with uAssignment := s.uAssignment.set! uidx (some u) }
    return true

def checkMVar (p : Expr) (e : Expr) : UnifyM Bool := do
  if (← read).unify && e.getAppFn.isMVar then
    pushPending p e
    return true
  else
    return false

def processLevel (u : Level) (v : Level) : UnifyM Bool := do
  match u, v with
  | .zero, .zero => return true
  | .succ u, .succ v => processLevel u v
  | .zero, .succ _ => return false
  | .succ _, .zero => return false
  | .zero, .max v₁ v₂ => processLevel .zero v₁ <&&> processLevel .zero v₂
  | .max u₁ u₂, .zero => processLevel u₁ .zero <&&> processLevel u₂ .zero
  | .zero, .imax _ v => processLevel .zero v
  | .imax _ u, .zero => processLevel u .zero
  | .max u₁ u₂, .max v₁ v₂ => processLevel u₁ v₁ <&&> processLevel u₂ v₂
  | .imax u₁ u₂, .imax v₁ v₂ => processLevel u₁ v₁ <&&> processLevel u₂ v₂
  | .param uName, _ =>
    if let some uidx := isUVar? uName then
      assignLevel uidx v
    else if u == v then
      return true
    else if v.isMVar && (← read).unify then
      pushLevelPending u v
      return true
    else
      return false
  | .mvar _, _ | _, .mvar _ =>
    if (← read).unify then
      pushLevelPending u v
      return true
    else
      return false
  | _, _ => return false

def processLevels (us : List Level) (vs : List Level) : UnifyM Bool := do
  match us, vs with
  | [],    []    => return true
  | [],    _::_  => return false
  | _::_,  []    => return false
  | u::us, v::vs => processLevel u v <&&> processLevels us vs

partial def process (p : Expr) (e : Expr) : UnifyM Bool := do
  match p with
  | .bvar bidx => assignExpr bidx e
  | .mdata _ p => process p e
  | .const declName us =>
    processConst declName us e <||> checkMVar p e
  | .sort u =>
    processSort u e <||> checkMVar p e
  | .app .. =>
    processApp p e <||> checkMVar p e
  | .forallE .. | .lam .. =>
    pushPending p e
    return true
  | .proj .. =>
    reportIssue! "unexpected kernel projection term during unification/matching{indentExpr e}\npre-process and fold them as projection applications"
    return false
  | .mvar _ | .fvar _ | .lit _ =>
    pure (p == e) <||> checkMVar p e
  | .letE .. => unreachable!
where
  processApp (p : Expr) (e : Expr) : UnifyM Bool := do
    -- **TODO**: Skip instance arguments, and process later
    -- **TODO**: Skip proof arguments
    let .app fp ap := p | process p e
    let .app fe ae := e | return false
    unless (← processApp fp fe) do return false
    process ap ae
  processConst (declName : Name) (us : List Level) (e : Expr) : UnifyM Bool := do
    let .const declName' us' := e | return false
    unless declName == declName' do return false
    processLevels us us'
  processSort (u : Level) (e : Expr) : UnifyM Bool := do
    let .sort v := e | return false
    processLevel u v

def noPending : UnifyM Bool := do
  let s ← get
  return s.ePending.isEmpty && s.uPending.isEmpty

def mkPreResult : UnifyM Unit := do
  let us ← (← get).uAssignment.toList.mapM fun
    | some val => pure val
    | none => mkFreshLevelMVar
  let pattern := (← read).pattern
  let varTypes := pattern.varTypes
  let eAssignment := (← get).eAssignment
  let mut args := #[]
  for h : i in *...eAssignment.size do
    if let .some val := eAssignment[i] then
      args := args.push val
    else
      let type := varTypes[i]!
      let type := type.instantiateLevelParams pattern.levelParams us
      let type ← shareCommon type
      let type ← instantiateRevS type args
      let mvar ← mkFreshExprSyntheticOpaqueMVar type
      let mvar ← shareCommon mvar
      args := args.push mvar
  modify fun s => { s with args, us }

def processPending : UnifyM Bool := do
  if (← noPending) then
    return true
  throwError "NIY: pending constraints"

abbrev run (pattern : Pattern) (unify : Bool) (k : UnifyM α) : SymM α := do
  let eAssignment := pattern.varTypes.map fun _ => none
  let uAssignment := pattern.levelParams.toArray.map fun _ => none
  k { unify, pattern } |>.run' { eAssignment, uAssignment }

public structure MatchUnifyResult where
  us : List Level
  args : Array Expr

def mkResult : UnifyM MatchUnifyResult := do
  let s ← get
  return { s with }

def main (p : Pattern) (e : Expr) (unify : Bool) : SymM (Option (MatchUnifyResult)) :=
  run p unify do
    unless (← process p.pattern e) do return none
    mkPreResult
    -- **TODO** synthesize instance arguments
    unless (← processPending) do return none
    return some (← mkResult)

public def Pattern.match? (p : Pattern) (e : Expr) : SymM (Option (MatchUnifyResult)) :=
  main p e (unify := false)

public def Pattern.unify? (p : Pattern) (e : Expr) : SymM (Option (MatchUnifyResult)) :=
  main p e (unify := true)

end Lean.Meta.Sym
