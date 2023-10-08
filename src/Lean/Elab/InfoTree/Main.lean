/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Meta.PPGoal

namespace Lean.Elab.ContextInfo

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

def CompletionInfo.stx : CompletionInfo → Syntax
  | dot i .. => i.stx
  | id stx .. => stx
  | dotId stx .. => stx
  | fieldId stx .. => stx
  | namespaceId stx => stx
  | option stx => stx
  | endSection stx .. => stx
  | tactic stx .. => stx

def CustomInfo.format : CustomInfo → Format
  | i => f!"CustomInfo({i.value.typeName})"

instance : ToFormat CustomInfo := ⟨CustomInfo.format⟩

partial def InfoTree.findInfo? (p : Info → Bool) (t : InfoTree) : Option Info :=
  match t with
  | context _ t => findInfo? p t
  | node i ts   =>
    if p i then
      some i
    else
      ts.findSome? (findInfo? p)
  | _ => none

/-- Instantiate the holes on the given `tree` with the assignment table.
(analogous to instantiating the metavariables in an expression) -/
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
    x.toIO { options := info.options, currNamespace := info.currNamespace, openDecls := info.openDecls, fileName := "<InfoTree>", fileMap := default }
           { env := info.env, ngen := info.ngen }
  return a

def ContextInfo.toPPContext (info : ContextInfo) (lctx : LocalContext) : PPContext :=
  { env  := info.env, mctx := info.mctx, lctx := lctx,
    opts := info.options, currNamespace := info.currNamespace, openDecls := info.openDecls }

def ContextInfo.ppSyntax (info : ContextInfo) (lctx : LocalContext) (stx : Syntax) : IO Format := do
  ppTerm (info.toPPContext lctx) ⟨stx⟩  -- HACK: might not be a term

private def formatStxRange (ctx : ContextInfo) (stx : Syntax) : Format :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  f!"{fmtPos pos stx.getHeadInfo}-{fmtPos endPos stx.getTailInfo}"
where fmtPos pos info :=
  let pos := format <| ctx.fileMap.toPosition pos
  match info with
  | .original ..                      => pos
  | .synthetic (canonical := true) .. => f!"{pos}†!"
  | _                                 => f!"{pos}†"

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
  | .dot i (expectedType? := expectedType?) .. => return f!"[.] {← i.format ctx} : {expectedType?}"
  | .id stx _ _ lctx expectedType? => ctx.runMetaM lctx do return f!"[.] {← ctx.ppSyntax lctx stx} : {expectedType?} @ {formatStxRange ctx info.stx}"
  | _ => return f!"[.] {info.stx} @ {formatStxRange ctx info.stx}"

def CommandInfo.format (ctx : ContextInfo) (info : CommandInfo) : IO Format := do
  return f!"command @ {formatElabInfo ctx info.toElabInfo}"

def OptionInfo.format (ctx : ContextInfo) (info : OptionInfo) : IO Format := do
  return f!"option {info.optionName} @ {formatStxRange ctx info.stx}"

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

def UserWidgetInfo.format (info : UserWidgetInfo) : Format :=
  f!"UserWidget {info.widgetId}\n{Std.ToFormat.format info.props}"

def FVarAliasInfo.format (info : FVarAliasInfo) : Format :=
  f!"FVarAlias {info.userName.eraseMacroScopes}"

def FieldRedeclInfo.format (ctx : ContextInfo) (info : FieldRedeclInfo) : Format :=
  f!"FieldRedecl @ {formatStxRange ctx info.stx}"

def Info.format (ctx : ContextInfo) : Info → IO Format
  | ofTacticInfo i         => i.format ctx
  | ofTermInfo i           => i.format ctx
  | ofCommandInfo i        => i.format ctx
  | ofMacroExpansionInfo i => i.format ctx
  | ofOptionInfo i         => i.format ctx
  | ofFieldInfo i          => i.format ctx
  | ofCompletionInfo i     => i.format ctx
  | ofUserWidgetInfo i     => pure <| i.format
  | ofCustomInfo i         => pure <| Std.ToFormat.format i
  | ofFVarAliasInfo i      => pure <| i.format
  | ofFieldRedeclInfo i    => pure <| i.format ctx

def Info.toElabInfo? : Info → Option ElabInfo
  | ofTacticInfo i         => some i.toElabInfo
  | ofTermInfo i           => some i.toElabInfo
  | ofCommandInfo i        => some i.toElabInfo
  | ofMacroExpansionInfo _ => none
  | ofOptionInfo _         => none
  | ofFieldInfo _          => none
  | ofCompletionInfo _     => none
  | ofUserWidgetInfo _     => none
  | ofCustomInfo _         => none
  | ofFVarAliasInfo _      => none
  | ofFieldRedeclInfo _    => none

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
  | hole id     => return .nestD f!"• ?{toString id.name}"
  | context i t => format t i
  | node i cs   => match ctx? with
    | none => return "• <context-not-available>"
    | some ctx =>
      let fmt ← i.format ctx
      if cs.size == 0 then
        return .nestD f!"• {fmt}"
      else
        let ctx? := i.updateContext? ctx?
        return .nestD f!"• {fmt}{Std.Format.prefixJoin .line (← cs.toList.mapM fun c => format c ctx?)}"

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

def addConstInfo [MonadEnv m] [MonadError m]
    (stx : Syntax) (n : Name) (expectedType? : Option Expr := none) : m Unit := do
  pushInfoLeaf <| .ofTermInfo {
    elaborator := .anonymous
    lctx := .empty
    expr := (← mkConstWithLevelParams n)
    stx
    expectedType?
  }

/-- This does the same job as `resolveGlobalConstNoOverload`; resolving an identifier
syntax to a unique fully resolved name or throwing if there are ambiguities.
But also adds this resolved name to the infotree. This means that when you hover
over a name in the sourcefile you will see the fully resolved name in the hover info.-/
def resolveGlobalConstNoOverloadWithInfo [MonadResolveName m] [MonadEnv m] [MonadError m]
    (id : Syntax) (expectedType? : Option Expr := none) : m Name := do
  let n ← resolveGlobalConstNoOverload id
  if (← getInfoState).enabled then
    -- we do not store a specific elaborator since identifiers are special-cased by the server anyway
    addConstInfo id n expectedType?
  return n

/-- Similar to `resolveGlobalConstNoOverloadWithInfo`, except if there are multiple name resolutions then it returns them as a list. -/
def resolveGlobalConstWithInfos [MonadResolveName m] [MonadEnv m] [MonadError m]
    (id : Syntax) (expectedType? : Option Expr := none) : m (List Name) := do
  let ns ← resolveGlobalConst id
  if (← getInfoState).enabled then
    for n in ns do
      addConstInfo id n expectedType?
  return ns

/-- Similar to `resolveGlobalName`, but it also adds the resolved name to the info tree. -/
def resolveGlobalNameWithInfos [MonadResolveName m] [MonadEnv m] [MonadError m]
    (ref : Syntax) (id : Name) : m (List (Name × List String)) := do
  let ns ← resolveGlobalName id
  if (← getInfoState).enabled then
    for (n, _) in ns do
      addConstInfo ref n
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
          | Sum.inl info   => treesSaved.push <| InfoTree.node info trees
          | Sum.inr mvarId => treesSaved.push <| InfoTree.hole mvarId
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
    Prod.fst <$> MonadFinally.tryFinally' x fun _ => modifyInfoState fun s =>
      if h : s.trees.size > 0 then
        have : s.trees.size - 1 < s.trees.size := Nat.sub_lt h (by decide)
        { s with trees := treesSaved, assignment := s.assignment.insert mvarId s.trees[s.trees.size - 1] }
      else
        { s with trees := treesSaved }
  else
    x

def enableInfoTree [MonadInfoTree m] (flag := true) : m Unit :=
  modifyInfoState fun s => { s with enabled := flag }

def withEnableInfoTree [Monad m] [MonadInfoTree m] [MonadFinally m] (flag : Bool) (x : m α) : m α := do
  let saved := (← getInfoState).enabled
  try
    enableInfoTree flag
    x
  finally
    enableInfoTree saved

def getInfoTrees [MonadInfoTree m] [Monad m] : m (PersistentArray InfoTree) :=
  return (← getInfoState).trees

end Lean.Elab
