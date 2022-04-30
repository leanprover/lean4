/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Data.Position
import Lean.Expr
import Lean.Message
import Lean.Data.Json
import Lean.Meta.Basic
import Lean.Meta.PPGoal

namespace Lean.Elab

open Std (PersistentArray PersistentArray.empty PersistentHashMap)

/-- Context after executing `liftTermElabM`.
   Note that the term information collected during elaboration may contain metavariables, and their
   assignments are stored at `mctx`. -/
structure ContextInfo where
  env           : Environment
  fileMap       : FileMap
  mctx          : MetavarContext := {}
  options       : Options        := {}
  currNamespace : Name           := Name.anonymous
  openDecls     : List OpenDecl  := []
  ngen          : NameGenerator -- We must save the name generator to implement `ContextInfo.runMetaM` and making we not create `MVarId`s used in `mctx`.
  deriving Inhabited

namespace ContextInfo

variable [Monad m] [MonadEnv m] [MonadMCtx m] [MonadOptions m] [MonadResolveName m] [MonadNameGenerator m]

def saveNoFileMap : m ContextInfo := return {
    env           := (← getEnv)
    fileMap       := default
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    ngen          := (← getNGen)
  }

def save [MonadFileMap m] : m ContextInfo := do
  let ctx ← saveNoFileMap
  return { ctx with fileMap := (← getFileMap) }

end ContextInfo

/-- An elaboration step -/
structure ElabInfo where
  elaborator : Name
  stx : Syntax
  deriving Inhabited

structure TermInfo extends ElabInfo where
  lctx : LocalContext -- The local context when the term was elaborated.
  expectedType? : Option Expr
  expr : Expr
  isBinder : Bool := false
  deriving Inhabited

structure CommandInfo extends ElabInfo where
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
  /-- Name of the projection. -/
  projName  : Name
  /-- Name of the field as written. -/
  fieldName : Name
  lctx      : LocalContext
  val       : Expr
  stx       : Syntax
  deriving Inhabited

/-- The information needed to render the tactic state in the infoview.

    We store the list of goals before and after the execution of a tactic.
    We also store the metavariable context at each time since we want metavariables
    unassigned at tactic execution time to be displayed as `?m...`. -/
structure TacticInfo extends ElabInfo where
  mctxBefore  : MetavarContext
  goalsBefore : List MVarId
  mctxAfter   : MetavarContext
  goalsAfter  : List MVarId
  deriving Inhabited

structure MacroExpansionInfo where
  lctx   : LocalContext -- The local context when the macro was expanded.
  stx    : Syntax
  output : Syntax
  deriving Inhabited

structure CustomInfo where
  stx : Syntax
  json : Json
  deriving Inhabited

def CustomInfo.format : CustomInfo → Format
  | i => Std.ToFormat.format i.json

instance : ToFormat CustomInfo := ⟨CustomInfo.format⟩

/-- Header information for a node in `InfoTree`. -/
inductive Info where
  | ofTacticInfo (i : TacticInfo)
  | ofTermInfo (i : TermInfo)
  | ofCommandInfo (i : CommandInfo)
  | ofMacroExpansionInfo (i : MacroExpansionInfo)
  | ofFieldInfo (i : FieldInfo)
  | ofCompletionInfo (i : CompletionInfo)
  | ofCustomInfo (i : CustomInfo)
  deriving Inhabited

/-- The InfoTree is a structure that is generated during elaboration and used
    by the language server to look up information about objects at particular points
    in the Lean document. For example, tactic information and expected type information in
    the infoview and information about completions.

    The infotree consists of nodes which may have child nodes. Each node
    has an `Info` object that contains details about what kind of information
    is present. Each `Info` object also contains a `Syntax` instance, this is used to
    map positions in the Lean document to particular info objects.

    An example of a function that extracts information from an infotree for a given
    position is `InfoTree.goalsAt?` which finds `TacticInfo`.

    Information concerning expressions requires that a context also be saved.
    `context` nodes store a local context that is used to process expressions
    in nodes below.

    Because the info tree is generated during elaboration, some parts of the infotree
    for a particular piece of syntax may not be ready yet. Hence InfoTree supports metavariable-like
    `hole`s which are filled in later in the same way that unassigned metavariables are.
-/
inductive InfoTree where
  | /-- The context object is created by `liftTermElabM` at `Command.lean` -/
    context (i : ContextInfo) (t : InfoTree)
  | /-- The children contain information for nested term elaboration and tactic evaluation -/
    node (i : Info) (children : PersistentArray InfoTree)
  | /-- The elaborator creates holes (aka metavariables) for tactics and postponed terms -/
    hole (mvarId : MVarId)
  deriving Inhabited

partial def InfoTree.findInfo? (p : Info → Bool) (t : InfoTree) : Option Info :=
  match t with
  | context _ t => findInfo? p t
  | node i ts   =>
    if p i then
      some i
    else
      ts.findSome? (findInfo? p)
  | _ => none

/-- This structure is the state that is being used to build an InfoTree object.
During elaboration, some parts of the info tree may be `holes` which need to be filled later.
The `assignments` field is used to assign these holes.
The `trees` field is a list of pending child trees for the infotree node currently being built.

You should not need to use `InfoState` directly, instead infotrees should be built with the help of the methods here
such as `pushInfoLeaf` to create leaf nodes and `withInfoContext` to create a nested child node.

To see how `trees` is used, look at the function body of `withInfoContext'`.
-/
structure InfoState where
  /-- Whether info trees should be recorded. -/
  enabled    : Bool := true
  /-- Map from holes in the infotree to child infotrees. -/
  assignment : PersistentHashMap MVarId InfoTree := {}
  /-- Pending child trees of a node. -/
  trees      : PersistentArray InfoTree := {}
  deriving Inhabited

class MonadInfoTree (m : Type → Type)  where
  getInfoState    : m InfoState
  modifyInfoState : (InfoState → InfoState) → m Unit

export MonadInfoTree (getInfoState modifyInfoState)

instance [MonadLift m n] [MonadInfoTree m] : MonadInfoTree n where
  getInfoState      := liftM (getInfoState : m _)
  modifyInfoState f := liftM (modifyInfoState f : m _)

/-- Instantiate the holes on the given `tree` with the assignment table.
(analoguous to instantiating the metavariables in an expression) -/
partial def InfoTree.substitute (tree : InfoTree) (assignment : PersistentHashMap MVarId InfoTree) : InfoTree :=
  match tree with
  | node i c => node i <| c.map (substitute · assignment)
  | context i t => context i (substitute t assignment)
  | hole id  => match assignment.find? id with
    | none      => hole id
    | some tree => substitute tree assignment

def ContextInfo.runMetaM (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) : IO α := do
  let x := x.run { lctx := lctx } { mctx := info.mctx }
  /-
    We must execute `x` using the `ngen` stored in `info`. Otherwise, we may create `MVarId`s and `FVarId`s that
    have been used in `lctx` and `info.mctx`.
  -/
  let ((a, _), _) ←
    x.toIO { options := info.options, currNamespace := info.currNamespace, openDecls := info.openDecls }
           { env := info.env, ngen := info.ngen }
  return a

def ContextInfo.toPPContext (info : ContextInfo) (lctx : LocalContext) : PPContext :=
  { env  := info.env, mctx := info.mctx, lctx := lctx,
    opts := info.options, currNamespace := info.currNamespace, openDecls := info.openDecls }

def ContextInfo.ppSyntax (info : ContextInfo) (lctx : LocalContext) (stx : Syntax) : IO Format := do
  ppTerm (info.toPPContext lctx) stx

private def formatStxRange (ctx : ContextInfo) (stx : Syntax) : Format :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  f!"{fmtPos pos stx.getHeadInfo}-{fmtPos endPos stx.getTailInfo}"
where fmtPos pos info :=
    let pos := format <| ctx.fileMap.toPosition pos
    match info with
    | SourceInfo.original ..  => pos
    | _                       => f!"{pos}†"

private def formatElabInfo (ctx : ContextInfo) (info : ElabInfo) : Format :=
  if info.elaborator.isAnonymous then
    formatStxRange ctx info.stx
  else
    f!"{formatStxRange ctx info.stx} @ {info.elaborator}"

def TermInfo.runMetaM (info : TermInfo) (ctx : ContextInfo) (x : MetaM α) : IO α :=
  ctx.runMetaM info.lctx x

def TermInfo.format (ctx : ContextInfo) (info : TermInfo) : IO Format := do
  info.runMetaM ctx do
    let ty : Format ← try
      Meta.ppExpr (← Meta.inferType info.expr)
    catch _ =>
      pure "<failed-to-infer-type>"
    return f!"{← Meta.ppExpr info.expr} {if info.isBinder then "(isBinder := true) " else ""}: {ty} @ {formatElabInfo ctx info.toElabInfo}"

def CompletionInfo.format (ctx : ContextInfo) (info : CompletionInfo) : IO Format :=
  match info with
  | CompletionInfo.dot i (expectedType? := expectedType?) .. => return f!"[.] {← i.format ctx} : {expectedType?}"
  | CompletionInfo.id stx _ _ lctx expectedType? => ctx.runMetaM lctx do return f!"[.] {stx} : {expectedType?} @ {formatStxRange ctx info.stx}"
  | _ => return f!"[.] {info.stx} @ {formatStxRange ctx info.stx}"

def CommandInfo.format (ctx : ContextInfo) (info : CommandInfo) : IO Format := do
  return f!"command @ {formatElabInfo ctx info.toElabInfo}"

def FieldInfo.format (ctx : ContextInfo) (info : FieldInfo) : IO Format := do
  ctx.runMetaM info.lctx do
    return f!"{info.fieldName} : {← Meta.ppExpr (← Meta.inferType info.val)} := {← Meta.ppExpr info.val} @ {formatStxRange ctx info.stx}"

def ContextInfo.ppGoals (ctx : ContextInfo) (goals : List MVarId) : IO Format :=
  if goals.isEmpty then
    return "no goals"
  else
    ctx.runMetaM {} (return Std.Format.prefixJoin "\n" (← goals.mapM (Meta.ppGoal ·)))

def TacticInfo.format (ctx : ContextInfo) (info : TacticInfo) : IO Format := do
  let ctxB := { ctx with mctx := info.mctxBefore }
  let ctxA := { ctx with mctx := info.mctxAfter }
  let goalsBefore ← ctxB.ppGoals info.goalsBefore
  let goalsAfter  ← ctxA.ppGoals info.goalsAfter
  return f!"Tactic @ {formatElabInfo ctx info.toElabInfo}\n{info.stx}\nbefore {goalsBefore}\nafter {goalsAfter}"

def MacroExpansionInfo.format (ctx : ContextInfo) (info : MacroExpansionInfo) : IO Format := do
  let stx    ← ctx.ppSyntax info.lctx info.stx
  let output ← ctx.ppSyntax info.lctx info.output
  return f!"Macro expansion\n{stx}\n===>\n{output}"

def Info.format (ctx : ContextInfo) : Info → IO Format
  | ofTacticInfo i         => i.format ctx
  | ofTermInfo i           => i.format ctx
  | ofCommandInfo i        => i.format ctx
  | ofMacroExpansionInfo i => i.format ctx
  | ofFieldInfo i          => i.format ctx
  | ofCompletionInfo i     => i.format ctx
  | ofCustomInfo i         => pure <| Std.ToFormat.format i

def Info.toElabInfo? : Info → Option ElabInfo
  | ofTacticInfo i         => some i.toElabInfo
  | ofTermInfo i           => some i.toElabInfo
  | ofCommandInfo i        => some i.toElabInfo
  | ofMacroExpansionInfo i => none
  | ofFieldInfo i          => none
  | ofCompletionInfo i     => none
  | ofCustomInfo i         => none

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
  | hole id     => return toString id.name
  | context i t => format t i
  | node i cs   => match ctx? with
    | none => return "<context-not-available>"
    | some ctx =>
      let fmt ← i.format ctx
      if cs.size == 0 then
        return fmt
      else
        let ctx? := i.updateContext? ctx?
        return f!"{fmt}{Std.Format.nestD <| Std.Format.prefixJoin (Std.format "\n") (← cs.toList.mapM fun c => format c ctx?)}"

section
variable [Monad m] [MonadInfoTree m]

@[inline] private def modifyInfoTrees (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
  modifyInfoState fun s => { s with trees := f s.trees }

/-- Returns the current array of InfoTrees and resets it to an empty array. -/
def getResetInfoTrees : m (PersistentArray InfoTree) := do
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

/-- This does the same job as resolveGlobalConstNoOverload; resolving an identifier
syntax to a unique fully resolved name or throwing if there are ambiguities.
But also adds this resolved name to the infotree. This means that when you hover
over a name in the sourcefile you will see the fully resolved name in the hover info.-/
def resolveGlobalConstNoOverloadWithInfo [MonadResolveName m] [MonadEnv m] [MonadError m] (id : Syntax) (expectedType? : Option Expr := none) : m Name := do
  let n ← resolveGlobalConstNoOverload id
  if (← getInfoState).enabled then
    -- we do not store a specific elaborator since identifiers are special-cased by the server anyway
    pushInfoLeaf <| Info.ofTermInfo { elaborator := Name.anonymous, lctx := LocalContext.empty, expr := (← mkConstWithLevelParams n), stx := id, expectedType? }
  return n

/-- Similar to resolveGlobalConstNoOverloadWithInfo, except if there are multiple name resolutions then it returns them as a list. -/
def resolveGlobalConstWithInfos [MonadResolveName m] [MonadEnv m] [MonadError m] (id : Syntax) (expectedType? : Option Expr := none) : m (List Name) := do
  let ns ← resolveGlobalConst id
  if (← getInfoState).enabled then
    for n in ns do
      pushInfoLeaf <| Info.ofTermInfo { elaborator := Name.anonymous, lctx := LocalContext.empty, expr := (← mkConstWithLevelParams n), stx := id, expectedType? }
  return ns

/-- Use this to descend a node on the infotree that is being built.

It saves the current list of trees `t₀` and resets it and then runs `x >>= mkInfo`, producing either an `i : Info` or a hole id.
Running `x >>= mkInfo` will modify the trees state and produce a new list of trees `t₁`.
In the `i : Info` case, `t₁` become the children of a node `node i t₁` that is appended to `t₀`.
 -/
def withInfoContext' [MonadFinally m] (x : m α) (mkInfo : α → m (Sum Info MVarId)) : m α := do
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

/-- Saves the current list of trees `t₀`, runs `x` to produce a new tree list `t₁` and
runs `mkInfoTree t₁` to get `n : InfoTree` and then restores the trees to be `t₀ ++ [n]`.-/
def withInfoTreeContext [MonadFinally m] (x : m α) (mkInfoTree : PersistentArray InfoTree → m InfoTree) : m α := do
  if (← getInfoState).enabled then
    let treesSaved ← getResetInfoTrees
    Prod.fst <$> MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let tree  ← mkInfoTree st.trees
      modifyInfoTrees fun _ => treesSaved.push tree
  else
    x

/-- Run `x` as a new child infotree node with header given by `mkInfo`. -/
@[inline] def withInfoContext [MonadFinally m] (x : m α) (mkInfo : m Info) : m α := do
  withInfoTreeContext x (fun trees => do return InfoTree.node (← mkInfo) trees)

/-- Resets the trees state `t₀`, runs `x` to produce a new trees
state `t₁` and sets the state to be `t₀ ++ (InfoTree.context Γ <$> t₁)`
where `Γ` is the context derived from the monad state. -/
def withSaveInfoContext [MonadNameGenerator m] [MonadFinally m] [MonadEnv m] [MonadOptions m] [MonadMCtx m] [MonadResolveName m] [MonadFileMap m] (x : m α) : m α := do
  if (← getInfoState).enabled then
    let treesSaved ← getResetInfoTrees
    Prod.fst <$> MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let trees ← st.trees.mapM fun tree => do
        let tree := tree.substitute st.assignment
        pure <| InfoTree.context (← ContextInfo.save) tree
      modifyInfoTrees fun _ => treesSaved ++ trees
  else
    x

def getInfoHoleIdAssignment? (mvarId : MVarId) : m (Option InfoTree) :=
  return (← getInfoState).assignment[mvarId]

def assignInfoHoleId (mvarId : MVarId) (infoTree : InfoTree) : m Unit := do
  assert! (← getInfoHoleIdAssignment? mvarId).isNone
  modifyInfoState fun s => { s with assignment := s.assignment.insert mvarId infoTree }
end

def withMacroExpansionInfo [MonadFinally m] [Monad m] [MonadInfoTree m] [MonadLCtx m] (stx output : Syntax) (x : m α) : m α :=
  let mkInfo : m Info := do
    return Info.ofMacroExpansionInfo {
      lctx   := (← getLCtx)
      stx, output
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
