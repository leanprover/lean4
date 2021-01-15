/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Leonardo de Moura
-/
import Lean.Data.Position
import Lean.Expr
import Lean.Message
import Lean.Data.Json
import Lean.Meta.Basic
import Lean.Meta.PPGoal

namespace Lean.Elab

open Std (PersistentArray PersistentArray.empty PersistentHashMap)

/- Context after executing `liftTermElabM`.
   Note that the term information collected during elaboration may contain metavariables, and their
   assignments are stored at `mctx`. -/
structure ContextInfo where
  env           : Environment
  fileMap       : FileMap
  mctx          : MetavarContext := {}
  options       : Options        := {}
  currNamespace : Name           := Name.anonymous
  openDecls     : List OpenDecl  := []
  deriving Inhabited

structure TermInfo where
  lctx : LocalContext -- The local context when the term was elaborated.
  expr : Expr
  stx  : Syntax
  deriving Inhabited

structure FieldInfo where
  name : Name
  lctx : LocalContext
  val  : Expr
  stx  : Syntax
  deriving Inhabited

/- We store the list of goals before and after the execution of a tactic.
   We also store the metavariable context at each time since, we want to unassigned metavariables
   at tactic execution time to be displayed as `?m...`. -/
structure TacticInfo where
  mctxBefore  : MetavarContext
  goalsBefore : List MVarId
  stx         : Syntax
  mctxAfter   : MetavarContext
  goalsAfter  : List MVarId
  deriving Inhabited

structure MacroExpansionInfo where
  lctx   : LocalContext -- The local context when the macro was expanded.
  before : Syntax
  after  : Syntax
  deriving Inhabited

inductive Info where
  | ofTacticInfo (i : TacticInfo)
  | ofTermInfo (i : TermInfo)
  | ofMacroExpansionInfo (i : MacroExpansionInfo)
  | ofFieldInfo (i : FieldInfo)
  deriving Inhabited

inductive InfoTree where
  | context (i : ContextInfo) (t : InfoTree) -- The context object is created by `liftTermElabM` at `Command.lean`
  | node (i : Info) (children : PersistentArray InfoTree) -- The children contains information for nested term elaboration and tactic evaluation
  | ofJson (j : Json) -- For user data
  | hole (mvarId : MVarId) -- The elaborator creates holes (aka metavariables) for tactics and postponed terms
  deriving Inhabited

structure InfoState where
  enabled    : Bool := false
  assignment : PersistentHashMap MVarId InfoTree := {} -- map from holeId to InfoTree
  trees      : PersistentArray InfoTree := {}
  deriving Inhabited

class MonadInfoTree (m : Type → Type)  where
  getInfoState    : m InfoState
  modifyInfoState : (InfoState → InfoState) → m Unit

export MonadInfoTree (getInfoState modifyInfoState)

instance (m n) [MonadLift m n] [MonadInfoTree m] : MonadInfoTree n where
  getInfoState      := liftM (getInfoState : m _)
  modifyInfoState f := liftM (modifyInfoState f : m _)

partial def InfoTree.substitute (tree : InfoTree) (assignment : PersistentHashMap MVarId InfoTree) : InfoTree :=
  match tree with
  | node i c => node i <| c.map (substitute · assignment)
  | context i t => context i (substitute t assignment)
  | ofJson j => ofJson j
  | hole id  => match assignment.find? id with
    | none      => hole id
    | some tree => substitute tree assignment

def ContextInfo.runMetaM (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) : IO α := do
  let x := x.run { lctx := lctx } { mctx := info.mctx }
  let ((a, _), _) ← x.toIO { options := info.options, currNamespace := info.currNamespace, openDecls := info.openDecls } { env := info.env }
  return a

def ContextInfo.toPPContext (info : ContextInfo) (lctx : LocalContext) : PPContext :=
  { env  := info.env, mctx := info.mctx, lctx := lctx,
    opts := info.options, currNamespace := info.currNamespace, openDecls := info.openDecls }

def ContextInfo.ppSyntax (info : ContextInfo) (lctx : LocalContext) (stx : Syntax) : IO Format := do
  ppTerm (info.toPPContext lctx) stx

def TermInfo.format (cinfo : ContextInfo) (info : TermInfo) : IO Format := do
  cinfo.runMetaM info.lctx do
    let pos    := info.stx.getPos.getD 0
    let endPos := info.stx.getTailPos.getD pos
    return f!"{← Meta.ppExpr info.expr} : {← Meta.ppExpr (← Meta.inferType info.expr)} @ {cinfo.fileMap.toPosition pos}-{cinfo.fileMap.toPosition endPos}"

def FieldInfo.format (cinfo : ContextInfo) (info : FieldInfo) : IO Format := do
  cinfo.runMetaM info.lctx do
    let pos    := info.stx.getPos.getD 0
    let endPos := info.stx.getTailPos.getD pos
    return f!"{info.name} : {← Meta.ppExpr (← Meta.inferType info.val)} := {← Meta.ppExpr info.val} @ {cinfo.fileMap.toPosition pos}-{cinfo.fileMap.toPosition endPos}"

def ContextInfo.ppGoals (cinfo : ContextInfo) (goals : List MVarId) : IO Format :=
  if goals.isEmpty then
    return "no goals"
  else
    cinfo.runMetaM {} (return Std.Format.prefixJoin "\n" (← goals.mapM Meta.ppGoal))

def TacticInfo.format (cinfo : ContextInfo) (info : TacticInfo) : IO Format := do
  let cinfoB := { cinfo with mctx := info.mctxBefore }
  let cinfoA := { cinfo with mctx := info.mctxAfter }
  let goalsBefore ← cinfoB.ppGoals info.goalsBefore
  let goalsAfter  ← cinfoA.ppGoals info.goalsAfter
  return f!"Tactic\nbefore {goalsBefore}\nafter {goalsAfter}"

def MacroExpansionInfo.format (cinfo : ContextInfo) (info : MacroExpansionInfo) : IO Format := do
  let before ← cinfo.ppSyntax info.lctx info.before
  let after  ← cinfo.ppSyntax info.lctx info.after
  return f!"Macro expansion\n{before}\n===>\n{after}"

def Info.format (cinfo : ContextInfo) : Info → IO Format
  | ofTacticInfo i         => i.format cinfo
  | ofTermInfo i           => i.format cinfo
  | ofMacroExpansionInfo i => i.format cinfo
  | ofFieldInfo i          => i.format cinfo

partial def InfoTree.format (tree : InfoTree) (cinfo? : Option ContextInfo := none) : IO Format := do
  match tree with
  | ofJson j    => return toString j
  | hole id     => return toString id
  | context i t => format t i
  | node i cs   => match cinfo? with
    | none => return "<context-not-available>"
    | some cinfo =>
      if cs.size == 0 then
        i.format cinfo
      else
        return f!"{← i.format cinfo}{Std.Format.nestD <| Std.Format.prefixJoin "\n" (← cs.toList.mapM fun c => format c cinfo?)}"

section
variables [Monad m] [MonadInfoTree m]

@[inline] private def modifyInfoTrees (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
  modifyInfoState fun s => { s with trees := f s.trees }

private def getResetInfoTrees : m (PersistentArray InfoTree) := do
  let trees := (← getInfoState).trees
  modifyInfoTrees fun _ => {}
  return trees

def pushInfoTree (t : InfoTree) : m Unit := do
  if (← getInfoState).enabled then
    modifyInfoTrees fun ts => ts.push t

def mkInfoNode (info : Info) : m Unit := do
  if (← getInfoState).enabled then
    modifyInfoTrees fun ts => PersistentArray.empty.push <| InfoTree.node info ts

@[inline] def withInfoContext' [MonadFinally m] (x : m α) (mkInfo : α → m (Sum Info MVarId)) : m α := do
  if (← getInfoState).enabled then
    let treesSaved ← getResetInfoTrees
    Prod.fst <$> MonadFinally.tryFinally' x fun a? => do
      match a? with
      | none   => modifyInfoTrees fun _ => treesSaved
      | some a => modifyInfoTrees fun trees =>
        match (← mkInfo a) with
        | Sum.inl info  => treesSaved.push <| InfoTree.node info trees
        | Sum.inr mvaId => treesSaved.push <| InfoTree.hole mvaId
  else
    x

@[inline] def withInfoContext [MonadFinally m] (x : m α) (mkInfo : m Info) : m α :=
  withInfoContext' x fun _ => return Sum.inl (← mkInfo)

def getInfoHoleIdAssignment? (mvarId : MVarId) : m (Option InfoTree) :=
  return (← getInfoState).assignment[mvarId]

def assignInfoHoleId (mvarId : MVarId) (infoTree : InfoTree) : m Unit := do
  assert! (← getInfoHoleIdAssignment? mvarId).isNone
  modifyInfoState fun s => { s with assignment := s.assignment.insert mvarId infoTree }
end

def withMacroExpansionInfo [MonadFinally m] [Monad m] [MonadInfoTree m] [MonadLCtx m] (before after : Syntax) (x : m α) : m α :=
  let mkInfo : m Info := do
    return Info.ofMacroExpansionInfo {
      lctx   := (← getLCtx)
      before := before
      after  := after
    }
  withInfoContext x mkInfo

@[inline] def withInfoHole [MonadFinally m] [Monad m] [MonadInfoTree m] (mvarId : MVarId) (x : m α) : m α := do
  if (← getInfoState).enabled then
    let treesSaved ← getResetInfoTrees
    Prod.fst <$> MonadFinally.tryFinally' x fun a? => do
      match a? with
      | none   => modifyInfoTrees fun _ => treesSaved
      | some a => modifyInfoState fun s =>
        assert! s.trees.size == 1 -- if size is not one, then API is being misused.
        { s with trees := treesSaved, assignment := s.assignment.insert mvarId s.trees[0] }
  else
    x

def enableInfoTree [MonadInfoTree m] (flag := true) : m Unit :=
  modifyInfoState fun s => { s with enabled := flag }

def getInfoTrees [MonadInfoTree m] [Monad m] : m (PersistentArray InfoTree) :=
  return (← getInfoState).trees

end Lean.Elab
