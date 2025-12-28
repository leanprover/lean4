/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Util.FoldConsts
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.IsClass
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

def preprocessType (type : Expr) : MetaM Expr := do
  let type ← unfoldReducible type
  let type ← Core.betaReduce type
  zetaReduce type

/--
Information about a single argument position in a function's type signature.

This is used during pattern matching to identify arguments that can be skipped
or handled specially (e.g., instance arguments can be synthesized, proof arguments
can be inferred).
-/
public structure PatternArgInfo where
  /-- `true` if this argument is a proof (its type is a `Prop`). -/
  isProof    : Bool
  /-- `true` if this argument is a type class instance. -/
  isInstance : Bool

/--
Information about a function symbol occurring in a pattern.

Stores which argument positions are proofs or instances, enabling optimizations
during pattern matching such as skipping proof arguments or deferring instance synthesis.
-/
public structure FunPatternInfo where
  /-- Information about each argument position. -/
  argsInfo : Array PatternArgInfo

/--
Analyzes the type signature of `declName` and returns information about which arguments
are proofs or instances. Returns `none` if no arguments are proofs or instances.
-/
def mkFunPatternInfo? (declName : Name) : MetaM (Option FunPatternInfo) := do
  let info ← getConstInfo declName
  let type ← preprocessType info.type
  forallTelescopeReducing type fun xs _ => do
    let env ← getEnv
    let mut argsInfo := #[]
    let mut found := false
    for x in xs do
      let type ← inferType x
      let isInstance := isClass? env type |>.isSome
      let isProof ← isProp type
      if isInstance || isProof then
        found := true
      argsInfo := argsInfo.push { isInstance, isProof }
    if found then
      return some { argsInfo }
    else
      return none

/--
Collects `FunPatternInfo` for all function symbols occurring in `pattern`.

Only includes functions that have at least one proof or instance argument.
-/
def mkFunInfosFor (pattern : Expr) : MetaM (AssocList Name FunPatternInfo) := do
  let cs := pattern.getUsedConstants
  let mut fnInfos := {}
  for declName in cs do
    if let some info ← mkFunPatternInfo? declName then
      fnInfos := fnInfos.insertNew declName info
  return fnInfos

public structure Pattern where
  levelParams  : List Name
  varTypes     : Array Expr
  pattern      : Expr
  fnInfos      : AssocList Name FunPatternInfo
  deriving Inhabited

def uvarPrefix : Name := `_uvar

def isUVar? (n : Name) : Option Nat := Id.run do
  let .num p idx := n | return none
  unless p == uvarPrefix do return none
  return some idx

public def mkPatternFromTheorem (declName : Name) : MetaM Pattern := do
  let info ← getConstInfo declName
  let levelParams := info.levelParams.mapIdx fun i _ => Name.num uvarPrefix i
  let us := levelParams.map mkLevelParam
  let type ← instantiateTypeLevelParams info.toConstantVal us
  let type ← preprocessType type
  -- **TODO**: save position of instance arguments
  let rec go (type : Expr) (varTypes : Array Expr) : MetaM Pattern := do
    match type with
    | .forallE _ d b _ => go b (varTypes.push d)
    | _ =>
      let pattern := type
      let fnInfos ← mkFunInfosFor pattern
      return { levelParams, varTypes, pattern, fnInfos }
  go type #[]

structure UnifyM.Context where
  pattern : Pattern
  unify   : Bool := true

structure UnifyM.State where
  eAssignment  : Array (Option Expr)   := #[]
  uAssignment  : Array (Option Level)  := #[]
  ePending     : Array (Expr × Expr)   := #[]
  uPending     : Array (Level × Level) := #[]
  iPending     : Array (Expr × Expr)   := #[]
  us           : List Level            := []
  args         : Array Expr            := #[]

abbrev UnifyM := ReaderT UnifyM.Context StateRefT UnifyM.State SymM

def pushPending (p : Expr) (e : Expr) : UnifyM Unit :=
  modify fun s => { s with ePending := s.ePending.push (p, e) }

def pushLevelPending (u : Level) (v : Level) : UnifyM Unit :=
  modify fun s => { s with uPending := s.uPending.push (u, v) }

def pushInstPending (p : Expr) (e : Expr) : UnifyM Unit :=
  modify fun s => { s with iPending := s.iPending.push (p, e) }

def assignExprIfUnassigned (bidx : Nat) (e : Expr) : UnifyM Unit := do
  let s ← get
  let i := s.eAssignment.size - bidx - 1
  if s.eAssignment[i]!.isNone then
    modify fun s => { s with eAssignment := s.eAssignment.set! i (some e) }

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
    let f := p.getAppFn
    let .const declName _ := f | processAppDefault p e
    let some info := (← read).pattern.fnInfos.find? declName | process.processAppDefault p e
    let numArgs := p.getAppNumArgs
    processAppWithInfo p e (numArgs - 1) info

  processAppWithInfo (p : Expr) (e : Expr) (i : Nat) (info : FunPatternInfo) : UnifyM Bool := do
    let .app fp ap := p | process p e
    let .app fe ae := e | return false
    unless (← processAppWithInfo fp fe (i - 1) info) do return false
    if h : i < info.argsInfo.size then
      let argInfo := info.argsInfo[i]
      if argInfo.isInstance then
        if let .bvar bidx := ap then
          assignExprIfUnassigned bidx ae
        else
          pushInstPending ap ae
        return true
      else if argInfo.isProof then
        if let .bvar bidx := ap then
          assignExprIfUnassigned bidx ae
        return true
      else
        process ap ae
    else
      process ap ae

  processAppDefault (p : Expr) (e : Expr) : UnifyM Bool := do
    let .app fp ap := p | process p e
    let .app fe ae := e | return false
    unless (← processAppDefault fp fe) do return false
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
  return s.ePending.isEmpty && s.uPending.isEmpty && s.iPending.isEmpty

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
      let type ← instantiateRevBetaS type args
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

/--
Attempts to match expression `e` against pattern `p` using purely syntactic matching.

Returns `some result` if matching succeeds, where `result` contains:
- `us`: Level assignments for the pattern's universe variables
- `args`: Expression assignments for the pattern's bound variables

Matching fails if:
- The term contains metavariables (use `unify?` instead)
- Structural mismatch after reducible unfolding

Instance arguments are deferred for later synthesis. Proof arguments are
skipped via proof irrelevance.
-/
public def Pattern.match? (p : Pattern) (e : Expr) : SymM (Option (MatchUnifyResult)) :=
  main p e (unify := false)

/--
Attempts to unify expression `e` against pattern `p`, allowing metavariables in `e`.

Returns `some result` if unification succeeds, where `result` contains:
- `us`: Level assignments for the pattern's universe variables
- `args`: Expression assignments for the pattern's bound variables

Unlike `match?`, this handles terms containing metavariables by deferring
constraints to Phase 2 unification. Use this when matching against goal
expressions that may contain unsolved metavariables.

Instance arguments are deferred for later synthesis. Proof arguments are
skipped via proof irrelevance.
-/
public def Pattern.unify? (p : Pattern) (e : Expr) : SymM (Option (MatchUnifyResult)) :=
  main p e (unify := true)

end Lean.Meta.Sym
