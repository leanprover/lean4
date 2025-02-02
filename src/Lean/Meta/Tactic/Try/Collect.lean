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

namespace Lean.Meta.Try.Collector

structure InductionCandidate where
  fvarId : FVarId
  val    : InductiveVal

structure FunIndCandidate where
  funIndDeclName : Name
  majors : Array Expr
  deriving Hashable, BEq

structure Result where
  /-- All constant symbols occurring in the gal. -/
  allConsts : Std.HashSet Name  := {}
  /-- Unfolding candiates. -/
  unfoldCandidates : Std.HashSet Name  := {}
  /-- Function induction candidates. -/
  funIndCandidates : Std.HashSet FunIndCandidate := {}
  /-- Induction candidates. -/
  indCandidates : Array InductionCandidate := #[]
  /-- Relevant declarations by `libSearch` -/
  libSearchResults : Std.HashSet (Name × Grind.EMatchTheoremKind) := {}

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

def getFunInductName (declName : Name) : Name :=
  declName ++ `induct

def getFunInduct? (declName : Name) : MetaM (Option Name) := do
  let .defnInfo _ ← getConstInfo declName | return none
  try
    let result ← realizeGlobalConstNoOverloadCore (getFunInductName declName)
    return some result
  catch _ =>
    return none

def isEligible (declName : Name) : M Bool := do
  if (← getConfig).main then
    return (← inCurrentModule declName)
  if (← getConfig).name then
    let ns ← getCurrNamespace
    return ns.isPrefixOf declName
  return false

def saveUnfoldCandidate (declName : Name) : M Unit := do
  if (← isEligible declName) then
    unless (← Grind.isEMatchTheorem (declName ++ `eq_def)) do
      modify fun s => { s with unfoldCandidates := s.unfoldCandidates.insert declName }

def visitConst (declName : Name) : M Unit := do
  saveConst declName
  saveUnfoldCandidate declName

def saveFunInduct (_e : Expr) (declName : Name) (_args : Array Expr) : M Unit := do
  if (← isEligible declName) then
    let some _indDeclName ← getFunInduct? declName
      | saveUnfoldCandidate declName; return ()
    -- TODO
    return ()

open LibrarySearch in
def saveLibSearchCandidates (e : Expr) : M Unit := do
  if (← getConfig).lib then
    for (declName, declMod) in (← libSearchFindDecls e) do
      unless (← Grind.isEMatchTheorem declName) do
        let kind := match declMod with
          | .none => .default
          | .mp => .leftRight
          | .mpr => .rightLeft
        modify fun s => { s with libSearchResults := s.libSearchResults.insert (declName, kind) }

def visitApp (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do
  saveFunInduct e declName args
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

def collect (mvarId : MVarId) (config : Try.Config) : MetaM Collector.Result := do
  unsafe Collector.main mvarId config

end Lean.Meta.Try
