/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.ForEachExpr
import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.Util

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
  libSearchResults : Std.HashSet (Expr × LibrarySearch.DeclMod) := {}

unsafe structure State where
  result : Result := {}
  visited : PtrSet Expr := mkPtrSet

unsafe abbrev M := StateRefT State MetaM

def getModuleName? (declName : Name) : CoreM (Option Name) := do
  let some modIdx := (← getEnv).getModuleIdxFor? declName | return none
  return (← getEnv).header.moduleNames[modIdx.toNat]!

def inCoreModule (declName : Name) : CoreM Bool := do
  let some moduleName ← getModuleName? declName | return false
  return (`Init).isPrefixOf moduleName || (`Std).isPrefixOf moduleName

def inCurrentModule (declName : Name) : CoreM Bool := do
  return (← getModuleName? declName).isNone

def getFunInductName (declName : Name) : Name :=
  declName ++ `induct

def getFunInduct? (declName : Name) : MetaM (Option Name) := do
  let .defnInfo _ ← getConstInfo declName | return none
  try
    let result ← realizeGlobalConstNoOverloadCore (getFunInductName declName)
    return some result
  catch _ =>
    return none

unsafe def saveConst (declName : Name) : M Unit := do
  modify fun s => { s with result.allConsts := s.result.allConsts.insert declName }

unsafe def visitConst (declName : Name) : M Unit := do
  saveConst declName
  return ()

unsafe def saveFunInduct (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do
  let some indDeclName ← getFunInduct? declName | return ()


unsafe def visitApp (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do

  return ()

unsafe def visit (e : Expr) : M Unit := do
  unless (← get).visited.contains e do
    modify fun s => { s with visited := s.visited.insert e }
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

unsafe def checkInductive (localDecl : LocalDecl) : M Unit := do
  let .const declName _ ← whnfD localDecl.type | return ()
  let .inductInfo val ← getConstInfo declName | return ()
  modify fun s => { s with result.indCandidates := s.result.indCandidates.push { fvarId := localDecl.fvarId, val } }

unsafe def main (mvarId : MVarId) (targetOnly : Bool := false) : MetaM Result := mvarId.withContext do
  let (_, s) ← go |>.run {}
  return s.result
where
  go : M Unit := do
    unless targetOnly do
      for localDecl in (← getLCtx) do
        unless localDecl.isAuxDecl do
          if let some val := localDecl.value? then
            visit val
          else
            checkInductive localDecl
            visit localDecl.type
    visit (← mvarId.getType)

end Collector

def collect (mvarId : MVarId) (targetOnly := false) : MetaM Collector.Result := do
  unsafe Collector.main mvarId targetOnly

end Lean.Meta.Try
