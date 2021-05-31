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
  expectedType? : Option Expr
  expr : Expr
  stx  : Syntax
  deriving Inhabited

structure CommandInfo where
  stx : Syntax
  deriving Inhabited

inductive CompletionInfo where
  | dot (termInfo : TermInfo) (field? : Option Syntax) (expectedType? : Option Expr)
  | id (stx : Syntax) (id : Name) (danglingDot : Bool) (lctx : LocalContext) (expectedType? : Option Expr)
  | namespaceId (stx : Syntax)
  | option (stx : Syntax)
  | endSection (stx : Syntax) (scopeNames : List String)
  | tactic (stx : Syntax) (goals : List MVarId)
  -- TODO `import`

def CompletionInfo.stx : CompletionInfo → Syntax
  | dot i .. => i.stx
  | id stx .. => stx
  | namespaceId stx => stx
  | option stx => stx
  | endSection stx .. => stx
  | tactic stx .. => stx

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
  | ofCommandInfo (i : CommandInfo)
  | ofMacroExpansionInfo (i : MacroExpansionInfo)
  | ofFieldInfo (i : FieldInfo)
  | ofCompletionInfo (i : CompletionInfo)
  deriving Inhabited

inductive InfoTree where
  | context (i : ContextInfo) (t : InfoTree) -- The context object is created by `liftTermElabM` at `Command.lean`
  | node (i : Info) (children : PersistentArray InfoTree) -- The children contains information for nested term elaboration and tactic evaluation
  | ofJson (j : Json) -- For user data
  | hole (mvarId : MVarId) -- The elaborator creates holes (aka metavariables) for tactics and postponed terms
  deriving Inhabited

partial def InfoTree.findInfo? (p : Info → Bool) (t : InfoTree) : Option InfoTree :=
  match t with
  | context _ t => findInfo? p t
  | node i ts   =>
    if p i then
      some t
    else
      ts.findSome? (findInfo? p)
  | _ => none

structure InfoState where
  enabled    : Bool := false
  assignment : PersistentHashMap MVarId InfoTree := {} -- map from holeId to InfoTree
  trees      : PersistentArray InfoTree := {}
  deriving Inhabited

class MonadInfoTree (m : Type → Type)  where
  getInfoState    : m InfoState
  modifyInfoState : (InfoState → InfoState) → m Unit

export MonadInfoTree (getInfoState modifyInfoState)

instance [MonadLift m n] [MonadInfoTree m] : MonadInfoTree n where
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

private def formatStxRange (ctx : ContextInfo) (stx : Syntax) : Format := do
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  return f!"{fmtPos pos stx.getHeadInfo}-{fmtPos endPos stx.getTailInfo}"
where fmtPos pos info :=
    let pos := format <| ctx.fileMap.toPosition pos
    match info with
    | SourceInfo.original ..  => pos
    | _                       => f!"{pos}†"

def TermInfo.runMetaM (info : TermInfo) (ctx : ContextInfo) (x : MetaM α) : IO α :=
  ctx.runMetaM info.lctx x

def TermInfo.format (ctx : ContextInfo) (info : TermInfo) : IO Format := do
  info.runMetaM ctx do
    try
      return f!"{← Meta.ppExpr info.expr} : {← Meta.ppExpr (← Meta.inferType info.expr)} @ {formatStxRange ctx info.stx}"
    catch _ =>
      return f!"{← Meta.ppExpr info.expr} : <failed-to-infer-type> @ {formatStxRange ctx info.stx}"

def CompletionInfo.format (ctx : ContextInfo) (info : CompletionInfo) : IO Format :=
  match info with
  | CompletionInfo.dot i (expectedType? := expectedType?) .. => return f!"[.] {← i.format ctx} : {expectedType?}"
  | CompletionInfo.id stx _ _ lctx expectedType? => ctx.runMetaM lctx do return f!"[.] {stx} : {expectedType?} @ {formatStxRange ctx info.stx}"
  | _ => return f!"[.] {info.stx} @ {formatStxRange ctx info.stx}"

def CommandInfo.format (ctx : ContextInfo) (info : CommandInfo) : IO Format := do
  return f!"command @ {formatStxRange ctx info.stx}"

def FieldInfo.format (ctx : ContextInfo) (info : FieldInfo) : IO Format := do
  ctx.runMetaM info.lctx do
    return f!"{info.name} : {← Meta.ppExpr (← Meta.inferType info.val)} := {← Meta.ppExpr info.val} @ {formatStxRange ctx info.stx}"

def ContextInfo.ppGoals (ctx : ContextInfo) (goals : List MVarId) : IO Format :=
  if goals.isEmpty then
    return "no goals"
  else
    ctx.runMetaM {} (return Std.Format.prefixJoin "\n" (← goals.mapM Meta.ppGoal))

def TacticInfo.format (ctx : ContextInfo) (info : TacticInfo) : IO Format := do
  let ctxB := { ctx with mctx := info.mctxBefore }
  let ctxA := { ctx with mctx := info.mctxAfter }
  let goalsBefore ← ctxB.ppGoals info.goalsBefore
  let goalsAfter  ← ctxA.ppGoals info.goalsAfter
  return f!"Tactic @ {formatStxRange ctx info.stx}\n{info.stx}\nbefore {goalsBefore}\nafter {goalsAfter}"

def MacroExpansionInfo.format (ctx : ContextInfo) (info : MacroExpansionInfo) : IO Format := do
  let before ← ctx.ppSyntax info.lctx info.before
  let after  ← ctx.ppSyntax info.lctx info.after
  return f!"Macro expansion\n{before}\n===>\n{after}"

def Info.format (ctx : ContextInfo) : Info → IO Format
  | ofTacticInfo i         => i.format ctx
  | ofTermInfo i           => i.format ctx
  | ofCommandInfo i        => i.format ctx
  | ofMacroExpansionInfo i => i.format ctx
  | ofFieldInfo i          => i.format ctx
  | ofCompletionInfo i     => i.format ctx

/--
  Helper function for propagating the tactic metavariable context to its children nodes.
  We need this function because we preserve `TacticInfo` nodes during backtracking *and* their
  children. Moreover, we backtrack the metavariable context to undo metavariable assignments.
  `TacticInfo` nodes save the metavariable context before/after the tactic application, and
  can be pretty printed without any extra information. This is not the case for `TermInfo` nodes.
  Without this function, the formatting method would often fail when processing `TermInfo` nodes
  that are children of `TacticInfo` nodes that have been preserved during backtracking.
  Saving the metavariable context at `TermInfo` nodes is also not a good option because
  at `TermInfo` creation time, the metavariable context often miss information, e.g.,
  a TC problem has not been resolved, a postponed subterm has not been elaborated, etc.

  See `Term.SavedState.restore`.
-/
def Info.updateContext? : Option ContextInfo → Info → Option ContextInfo
  | some ctx, ofTacticInfo i => some { ctx with mctx := i.mctxAfter }
  | ctx?, _ => ctx?

partial def InfoTree.format (tree : InfoTree) (ctx? : Option ContextInfo := none) : IO Format := do
  match tree with
  | ofJson j    => return toString j
  | hole id     => return toString id
  | context i t => format t i
  | node i cs   => match ctx? with
    | none => return "<context-not-available>"
    | some ctx =>
      let fmt ← i.format ctx
      if cs.size == 0 then
        return fmt
      else
        let ctx? := i.updateContext? ctx?
        return f!"{fmt}{Std.Format.nestD <| Std.Format.prefixJoin "\n" (← cs.toList.mapM fun c => format c ctx?)}"

section
variable [Monad m] [MonadInfoTree m]

@[inline] private def modifyInfoTrees (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
  modifyInfoState fun s => { s with trees := f s.trees }

private def getResetInfoTrees : m (PersistentArray InfoTree) := do
  let trees := (← getInfoState).trees
  modifyInfoTrees fun _ => {}
  return trees

def pushInfoTree (t : InfoTree) : m Unit := do
  if (← getInfoState).enabled then
    modifyInfoTrees fun ts => ts.push t

def pushInfoLeaf (t : Info) : m Unit := do
  if (← getInfoState).enabled then
    pushInfoTree <| InfoTree.node (children := {}) t

def addCompletionInfo (info : CompletionInfo) : m Unit := do
  pushInfoLeaf <| Info.ofCompletionInfo info

def resolveGlobalConstNoOverloadWithInfo [MonadResolveName m] [MonadEnv m] [MonadError m] (stx : Syntax) (id := stx.getId) (expectedType? : Option Expr := none) : m Name := do
  let n ← resolveGlobalConstNoOverload id
  if (← getInfoState).enabled then
    pushInfoLeaf <| Info.ofTermInfo { lctx := LocalContext.empty, expr := (← mkConstWithLevelParams n), stx, expectedType? }
  return n

def resolveGlobalConstWithInfos [MonadResolveName m] [MonadEnv m] [MonadError m] (stx : Syntax) (id := stx.getId) (expectedType? : Option Expr := none) : m (List Name) := do
  let ns ← resolveGlobalConst id
  if (← getInfoState).enabled then
    for n in ns do
      pushInfoLeaf <| Info.ofTermInfo { lctx := LocalContext.empty, expr := (← mkConstWithLevelParams n), stx, expectedType? }
  return ns

@[inline] def withInfoContext' [MonadFinally m] (x : m α) (mkInfo : α → m (Sum Info MVarId)) : m α := do
  if (← getInfoState).enabled then
    let treesSaved ← getResetInfoTrees
    Prod.fst <$> MonadFinally.tryFinally' x fun a? => do
      match a? with
      | none   => modifyInfoTrees fun _ => treesSaved
      | some a =>
        let info ← mkInfo a
        modifyInfoTrees fun trees =>
          match info with
          | Sum.inl info  => treesSaved.push <| InfoTree.node info trees
          | Sum.inr mvaId => treesSaved.push <| InfoTree.hole mvaId
  else
    x

@[inline] def withInfoTreeContext [MonadFinally m] (x : m α) (mkInfoTree : PersistentArray InfoTree → m InfoTree) : m α := do
  if (← getInfoState).enabled then
    let treesSaved ← getResetInfoTrees
    Prod.fst <$> MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let tree  ← mkInfoTree st.trees
      modifyInfoTrees fun _ => treesSaved.push tree
  else
    x

@[inline] def withInfoContext [MonadFinally m] (x : m α) (mkInfo : m Info) : m α := do
  withInfoTreeContext x (fun trees => do return InfoTree.node (← mkInfo) trees)

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
    Prod.fst <$> MonadFinally.tryFinally' x fun a? => modifyInfoState fun s =>
      if s.trees.size > 0 then
        { s with trees := treesSaved, assignment := s.assignment.insert mvarId s.trees[s.trees.size - 1] }
      else
        { s with trees := treesSaved }
  else
    x

def enableInfoTree [MonadInfoTree m] (flag := true) : m Unit :=
  modifyInfoState fun s => { s with enabled := flag }

def getInfoTrees [MonadInfoTree m] [Monad m] : m (PersistentArray InfoTree) :=
  return (← getInfoState).trees

end Lean.Elab
