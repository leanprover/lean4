/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Try
import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Grind.Cases
import Lean.Meta.Tactic.Grind.EMatchTheorem
import Lean.Meta.Tactic.FunIndInfo
import Lean.Meta.Tactic.FunIndCollect

namespace Lean.Meta.Try.Collector

structure InductionCandidate where
  fvarId : FVarId
  val    : InductiveVal

/-- `Set` with insertion order preserved. -/
structure OrdSet (α : Type) [Hashable α] [BEq α] where
  elems : Array α := #[]
  set : Std.HashSet α := {}
  deriving Inhabited

def OrdSet.insert {_ : Hashable α} {_ : BEq α} (s : OrdSet α) (a : α) : OrdSet α :=
  if s.set.contains a then
    s
  else
    let { elems, set } := s
    { elems := elems.push a, set := set.insert a }

def OrdSet.isEmpty {_ : Hashable α} {_ : BEq α} (s : OrdSet α) : Bool :=
  s.elems.isEmpty

structure Result where
  /-- All constant symbols occurring in the gal. -/
  allConsts : OrdSet Name  := {}
  /-- Unfolding candiates. -/
  unfoldCandidates : OrdSet Name  := {}
  /-- Equation function candiates. -/
  eqnCandidates : OrdSet Name  := {}
  /-- Function induction candidates -/
  funIndCandidates : FunInd.SeenCalls := {}
  /-- Induction candidates. -/
  indCandidates : Array InductionCandidate := #[]
  /-- Relevant declarations by `libSearch` -/
  libSearchResults : OrdSet (Name × Grind.EMatchTheoremKind) := {}

structure Context where
  config : Try.Config

abbrev M := ReaderT Context <| StateRefT Result MetaM

def getConfig : M Try.Config := do
  return (← read).config

def saveConst (declName : Name) : M Unit := do
  modify fun s => { s with allConsts := s.allConsts.insert declName }

/-- Returns `true` if `declName` is in the module being compiled. -/
def inCurrentModule (declName : Name) : CoreM Bool := do
  return ((← getEnv).getModuleIdxFor? declName).isNone

def isEligible (declName : Name) : M Bool := do
  if declName.hasMacroScopes then
    return false
  if (← getConfig).main then
    return (← inCurrentModule declName)
  if (← getConfig).name then
    let ns ← getCurrNamespace
    return ns.isPrefixOf declName
  return false

def saveEqnCandidate (declName : Name) : M Unit := do
  if (← isEligible declName) then
    let some eqns ← getEqnsFor? declName | return ()
    if eqns.isEmpty then return ()
    unless (← Grind.isEMatchTheorem eqns[0]!) do
      modify fun s => { s with eqnCandidates := s.eqnCandidates.insert declName }

def getEqDefDecl? (declName : Name) : MetaM (Option Name) := do
  let declName := declName ++ `eq_def
  if (← Grind.isEMatchTheorem declName) then return none
  try
    let result ← realizeGlobalConstNoOverloadCore declName
    return some result
  catch _ =>
    return none

def saveUnfoldCandidate (declName : Name) : M Unit := do
  if (← isEligible declName) then
    let some eqDefName ← getEqDefDecl? declName | return ()
    modify fun s => { s with unfoldCandidates := s.unfoldCandidates.insert eqDefName }

def visitConst (declName : Name) : M Unit := do
  saveConst declName
  saveUnfoldCandidate declName

def saveFunInd (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do
  if (← isEligible declName) then
    let sc := (← get).funIndCandidates
    let sc' ← sc.push e declName args
    modify fun s => { s with funIndCandidates := sc' }

open LibrarySearch in
def saveLibSearchCandidates (e : Expr) : M Unit := do
  if (← getConfig).harder then
    for (declName, declMod) in (← libSearchFindDecls e) do
      unless (← Grind.isEMatchTheorem declName) do
        let kind := match declMod with
          | .none => .default
          | .mp => .leftRight
          | .mpr => .rightLeft
        modify fun s => { s with libSearchResults := s.libSearchResults.insert (declName, kind) }

def visitApp (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do
  saveEqnCandidate declName
  saveFunInd e declName args
  saveUnfoldCandidate declName
  saveLibSearchCandidates e

def checkInductive (localDecl : LocalDecl) : M Unit := do
  let .const declName _ ← whnfD localDecl.type | return ()
  let .inductInfo val ← getConstInfo declName | return ()
  if (← isEligible declName) then
    unless (← Grind.isSplit declName) do
      modify fun s => { s with indCandidates := s.indCandidates.push { fvarId := localDecl.fvarId, val } }

unsafe abbrev Cache := PtrSet Expr

unsafe def visit (e : Expr) : StateRefT Cache M Unit := do
  unless (← get).contains e do
    modify fun s => s.insert e
    match e with
      | .const declName _ => visitConst declName
      | .forallE _ d b _  => visit d; visit b
      | .lam _ d b _      => visit d; visit b
      | .mdata _ b        => visit b
      | .letE _ t v b _   => visit t; visit v; visit b
      | .app ..           => e.withApp fun f args => do
        if let .const declName _ := f then
          saveConst declName
          unless e.hasLooseBVars do
            visitApp e declName args
        else
          visit f
        args.forM visit
      | .proj _ _ b       => visit b
      | _                 => return ()

unsafe def main (mvarId : MVarId) (config : Try.Config) : MetaM Result := mvarId.withContext do
  let (_, s) ← go |>.run mkPtrSet |>.run { config } |>.run {}
  return s
where
  go : StateRefT Cache M Unit := do
    unless (← getConfig).targetOnly do
      for localDecl in (← getLCtx) do
        unless localDecl.isAuxDecl do
          if let some val := localDecl.value? then
            visit val
          else
            checkInductive localDecl
            visit localDecl.type
    visit (← mvarId.getType)

end Collector

abbrev Info := Collector.Result

def collect (mvarId : MVarId) (config : Try.Config) : MetaM Info := do
  unsafe Collector.main mvarId config

end Lean.Meta.Try
