/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Tactic.Replace

/-!
# Tactics to manipulate `let` expressions
-/

open Lean Meta

namespace Lean.Meta

/-!
### `let` extraction

Extracting `let`s means to locate `let`/`letFun`s in a term and to extract them
from the term, extending the local context with new declarations in the process.
A related process is lifting `lets`, which means to move `let`/`letFun`s toward the root of a term.
-/

namespace ExtractLets

structure LocalDecl' where
  decl : LocalDecl
  /--
  If true, is a `let`, if false, is a `letFun`.
  Used in `lift` mode.
  -/
  isLet : Bool

structure State where
  /-- Names to use for local definitions for the extracted lets. -/
  givenNames : List Name
  /-- Saved declarations for the extracted `let`s. -/
  decls : Array LocalDecl' := #[]
  /-- Map from `let` values to fvars. To support the `merge` option. -/
  valueMap : ExprStructMap FVarId := {}
  deriving Inhabited

-- The `Bool` in the cache key is whether we are looking at a "top-level" expression.
abbrev M := ReaderT ExtractLetsConfig <| MonadCacheT (Bool × ExprStructEq) Expr <| StateRefT State MetaM

/-- Returns `true` if `nextName?` would return a name. -/
def hasNextName : M Bool := do
  return !(← read).onlyGivenNames || !(← get).givenNames.isEmpty

/-- Gets the next name to use for extracted `let`s -/
def nextName? : M (Option Name) := do
  let s ← get
  match s.givenNames, (← read).onlyGivenNames with
  | n :: ns, _      => set { s with givenNames := ns }; return n
  | []     , true   => return none
  | []     , false  => return `_

/--
Generate a name to use for a new local declaration, derived possibly from the given binder name.
Returns `none` iff `hasNextName` is false.
-/
def nextNameForBinderName? (binderName : Name) : M (Option Name) := do
  if let some n ← nextName? then
    if n != `_ then
      return n
    else
      if binderName.isAnonymous then
        -- Use a nicer binder name than `[anonymous]`, which can appear for example in `letFun x f` when `f` is not a lambda expression.
        mkFreshUserName `a
      else if (← read).preserveBinderNames || n.hasMacroScopes then
        return n
      else
        mkFreshUserName binderName
  else
    return none

/--
Returns 'true' if `e` does not depend on any of the fvars in `fvars`.
-/
def extractable (fvars : List Expr) (e : Expr) : Bool :=
  !e.hasAnyFVar (fvars.contains <| .fvar ·)

/--
Returns whether a let-like expression with the given type and value is extractable,
given the list `fvars` of binders that inhibit extraction.
-/
def isExtractableLet (fvars : List Expr) (n : Name) (t v : Expr) : M (Bool × Name) := do
  if (← hasNextName) && extractable fvars t && extractable fvars v then
    if let some n ← nextNameForBinderName? n then
      return (true, n)
  -- In lift mode, we temporarily extract non-extractable lets, but we do not make use of `givenNames` for them.
  -- These will be flushed as let/letFun expressions, and we wish to preserve the original binder name.
  if (← read).lift then
    return (true, n)
  return (false, n)

/--
Adds the `decl` to the `decls` list. Assumes that `decl` is an ldecl.
-/
def addDecl (decl : LocalDecl) (isLet : Bool) : M Unit := do
  let cfg ← read
  modify fun s => { s with
    decls := s.decls.push { decl, isLet }
    valueMap := if cfg.merge then s.valueMap.insert decl.value decl.fvarId else s.valueMap
  }

/--
Removes and returns all local declarations that (transitively) depend on `fvar`.
-/
def flushDecls (fvar : FVarId) : M (Array LocalDecl') := do
  let mut fvarSet : FVarIdSet := {}
  fvarSet := fvarSet.insert fvar
  let mut toSave := #[]
  let mut toFlush := #[]
  for ldecl in (← get).decls do
    if ldecl.decl.type.hasAnyFVar (fvarSet.contains ·) || ldecl.decl.value.hasAnyFVar (fvarSet.contains ·) then
      toFlush := toFlush.push ldecl
      fvarSet := fvarSet.insert ldecl.decl.fvarId
    else
      toSave := toSave.push ldecl
  modify fun s => { s with decls := toSave }
  return toFlush

/--
Ensures that the given local declarations are in context. Runs `k` in that context.
-/
def withEnsuringDeclsInContext [Monad m] [MonadControlT MetaM m] [MonadLCtx m] (decls : Array LocalDecl') (k : m α) : m α := do
  let lctx ← getLCtx
  let decls := decls |>.filter (!lctx.contains ·.decl.fvarId) |>.map (·.decl)
  withExistingLocalDecls decls.toList k

/--
Closes all the local declarations in `e`, creating `let` and `letFun` expressions.
Does not require that any of the declarations are in context.
Assumes that `e` contains no metavariables with local contexts that contain any of these metavariables
(the extraction procedure creates no new metavariables, so this is the case).

This should *not* be used when closing lets for new goal metavariables, since
1. The goal contains the decls in its local context, violating the assumption.
2. We need to use true `let`s in that case, since tactics may zeta-delta reduce these declarations.
-/
def mkLetDecls (decls : Array LocalDecl') (e : Expr) : MetaM Expr := do
  withEnsuringDeclsInContext decls do
    decls.foldrM (init := e) fun { decl, isLet } e => do
      if isLet then
        return .letE decl.userName decl.type decl.value (e.abstract #[decl.toExpr]) false
      else
        mkLetFun decl.toExpr decl.value e

/--
Makes sure the declaration for `fvarId` is marked with `isLet := true`.
Used in `lift + merge` mode to ensure that, after merging, if any version was a `let` then it's a `let` rather than a `letFun`.
-/
def ensureIsLet (fvarId : FVarId) : M Unit := do
  modify fun s => { s with
    decls := s.decls.map fun d =>
      if d.decl.fvarId == fvarId then { d with isLet := true } else d
  }

/--
Ensures that the given `fvarId` is in context by adding `decls` from the state.
Simplification: since we are not recording which decls depend on which, but we do know all dependencies
come before a particular decl, we add all the decls up to and including `fvarId`.

Used for `merge` feature.
-/
def withDeclInContext (fvarId : FVarId) (k : M α) : M α := do
  let decls := (← get).decls
  if (← getLCtx).contains fvarId then
    -- Is either pre-existing or already added.
    k
  else if let some idx := decls.findIdx? (·.decl.fvarId == fvarId) then
    withEnsuringDeclsInContext decls[0:idx+1] k
  else
    k

/--
Initializes the `valueMap` with all the local definitions that aren't implementation details.
Used for `merge` feature when `useContext` is enabled.
-/
def initializeValueMap : M Unit := do
  let lctx ← getLCtx
  lctx.forM fun decl => do
    if decl.isLet && !decl.isImplementationDetail then
      let value ← instantiateMVars decl.value
      modify fun s => { s with valueMap := s.valueMap.insert value decl.fvarId }

/--
Returns `true` if the expression contains a `let` expression or a `letFun`
(this does not verify that the `letFun`s are well-formed).
Its purpose is to be a check for whether a subexpression can be skipped.
-/
def containsLet (e : Expr) : Bool :=
  Option.isSome <| e.find? fun e' => e'.isLet || e'.isConstOf ``letFun

/--
Extracts lets from `e`.
- `fvars` is an array of all the local variables from going under binders,
  used to detect whether an expression is extractable. Extracted `let`s do not have their fvarids in this list.
  This is not part of the cache key since it's an optimization and in principle derivable.
- `topLevel` is whether we are still looking at the top-level expression.
  The body of an extracted top-level let is also considered to be top-level.
  This is part of the cache key since it affects what is extracted.

Note: the return value may refer to fvars that are not in the current local context, but they are in the `decls` list.
-/
partial def extractCore (fvars : List Expr) (e : Expr) (topLevel : Bool := false) : M Expr := do
  let cfg ← read
  if e.isAtomic then
    return e
  else if !cfg.descend && !topLevel then
    return e
  else
    checkCache (topLevel, (e : ExprStructEq)) fun _ => do
      if !containsLet e then
        return e
      -- Don't honor `proofs := false` or `types := false` for top-level lets, since it's confusing not having them be extracted.
      unless topLevel && (e.isLet || e.isLetFun || e.isMData) do
        if !cfg.proofs then
          if ← isProof e then
            return e
        if !cfg.types then
          if ← isType e then
            return e
      let whenDescend (k : M Expr) : M Expr := do if cfg.descend then k else pure e
      match e with
      | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => unreachable!
      | .mdata _ e'      => return e.updateMData! (← extractCore fvars e' (topLevel := topLevel))
      | .letE n t v b _  => extractLetLike true n t v b (fun t v b => pure <| e.updateLetE! t v b) (topLevel := topLevel)
      | .app ..          =>
        if e.isLetFun then
          extractLetFun e (topLevel := topLevel)
        else
          whenDescend do extractApp e.getAppFn e.getAppArgs
      | .proj _ _ s      => whenDescend do return e.updateProj! (← extractCore fvars s)
      | .lam n t b i     => whenDescend do extractBinder n t b i (fun t b => e.updateLambda! i t b)
      | .forallE n t b i => whenDescend do extractBinder n t b i (fun t b => e.updateForall! i t b)
where
  extractBinder (n : Name) (t b : Expr) (i : BinderInfo) (mk : Expr → Expr → Expr) : M Expr := do
    let t ← extractCore fvars t
    if (← read).underBinder then
      withLocalDecl n i t fun x => do
        let b ← extractCore (x :: fvars) (b.instantiate1 x)
        if (← read).lift then
          let toFlush ← flushDecls x.fvarId!
          let b ← mkLetDecls toFlush b
          return mk t (b.abstract #[x])
        else
          return mk t (b.abstract #[x])
    else
      return mk t b
  extractLetLike (isLet : Bool) (n : Name) (t v b : Expr) (mk : Expr → Expr → Expr → M Expr) (topLevel : Bool) : M Expr := do
    let cfg ← read
    let t ← extractCore fvars t
    let v ← extractCore fvars v
    if cfg.usedOnly && !b.hasLooseBVars then
      return ← extractCore fvars b (topLevel := topLevel)
    if cfg.merge then
      if let some fvarId := (← get).valueMap.get? v then
        if isLet && cfg.lift then ensureIsLet fvarId
        return ← withDeclInContext fvarId <|
          extractCore fvars (b.instantiate1 (.fvar fvarId)) (topLevel := topLevel)
    let (extract, n) ← isExtractableLet fvars n t v
    if !extract && (!cfg.underBinder || !cfg.descend) then
      return ← mk t v b
    withLetDecl n t v fun x => do
      if extract then
        addDecl (← x.fvarId!.getDecl) isLet
        extractCore fvars (b.instantiate1 x) (topLevel := topLevel)
      else
        let b ← extractCore (x :: fvars) (b.instantiate1 x)
        mk t v (b.abstract #[x])
  /-- `e` is the letFun expression -/
  extractLetFun (e : Expr) (topLevel : Bool) : M Expr := do
    let letFunE := e.getAppFn
    let β := e.getArg! 1
    let (n, t, v, b) := e.letFun?.get!
    extractLetLike false n t v b (topLevel := topLevel)
      (fun t v b =>
        -- Strategy: construct letFun directly rather than use `mkLetFun`.
        -- We don't update the `β` argument.
        return mkApp4 letFunE t β v (.lam n t b .default))
  extractApp (f : Expr) (args : Array Expr) : M Expr := do
    let cfg ← read
    if f.isConstOf ``letFun && args.size ≥ 4 then
      extractApp (mkAppN f args[0:4]) args[4:]
    else
      let f' ← extractCore fvars f
      if cfg.implicits then
        return mkAppN f' (← args.mapM (extractCore fvars))
      else
        let (paramInfos, _) ← instantiateForallWithParamInfos (← inferType f) args
        let mut args := args
        for i in [0:args.size] do
          if paramInfos[i]!.binderInfo.isExplicit then
            args := args.set! i (← extractCore fvars args[i]!)
        return mkAppN f' args

def extractTopLevel (e : Expr) : M Expr := do
  let e ← instantiateMVars e
  extractCore [] e (topLevel := true)

/--
Main entry point for extracting lets.
-/
def extract (es : Array Expr) : M (Array Expr) := do
  let cfg ← read
  if cfg.merge && cfg.useContext then
    initializeValueMap
  es.mapM extractTopLevel

end ExtractLets

/--
Implementation of the `extractLets` function.
- `es` is an array of terms that are valid in the current local context.
- `k` is a callback that is run in the updated local context with all relevant `let`s extracted
  and with the post-extraction expressions, and the remaining names from `givenNames`.
-/
private def extractLetsImp (es : Array Expr) (givenNames : List Name)
    (k : Array FVarId → Array Expr → List Name → MetaM α) (config : ExtractLetsConfig) : MetaM α := do
  let (es, st) ← ExtractLets.extract es |>.run config |>.run' {} |>.run { givenNames }
  let givenNames' := st.givenNames
  let decls := st.decls.map (·.decl)
  withExistingLocalDecls decls.toList <| k (decls.map (·.fvarId)) es givenNames'

/--
Extracts `let` and `letFun` expressions into local definitions,
evaluating `k` at the post-extracted expressions and the extracted fvarids, within a context containing those local declarations.
- The `givenNames` is a list of explicit names to use for extracted local declarations.
  If a name is `_` (or if there is no provided given name and `config.onlyGivenNames` is true) then uses a hygienic name
  based on the existing binder name.
-/
def extractLets [Monad m] [MonadControlT MetaM m] (es : Array Expr) (givenNames : List Name)
    (k : Array FVarId → Array Expr → List Name → m α) (config : ExtractLetsConfig := {}) : m α :=
  map3MetaM (fun k => extractLetsImp es givenNames k config) k

/--
Lifts `let` and `letFun` expressions in the given expression as far out as possible.
-/
def liftLets (e : Expr) (config : LiftLetsConfig := {}) : MetaM Expr := do
  let (es, st) ← ExtractLets.extract #[e] |>.run { config with onlyGivenNames := true } |>.run' {} |>.run { givenNames := [] }
  ExtractLets.mkLetDecls st.decls es[0]!

end Lean.Meta

private def throwMadeNoProgress (tactic : Name) (mvarId : MVarId) : MetaM α :=
  throwTacticEx tactic mvarId m!"made no progress"

/--
Extracts `let` and `letFun` expressions from the target,
returning `FVarId`s for the extracted let declarations along with the new goal.
- The `givenNames` is a list of explicit names to use for extracted local declarations.
  If a name is `_` (or if there is no provided given name and `config.onlyGivenNames` is true) then uses a hygienic name
  based on the existing binder name.
-/
def Lean.MVarId.extractLets (mvarId : MVarId) (givenNames : List Name) (config : ExtractLetsConfig := {}) :
    MetaM ((Array FVarId × List Name) × MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `extract_lets
    let ty ← mvarId.getType
    Meta.extractLets #[ty] givenNames (config := config) fun fvarIds es givenNames' => do
      let ty' := es[0]!
      if fvarIds.isEmpty && ty == ty' then
        throwMadeNoProgress `extract_lets mvarId
      let g ← mkFreshExprSyntheticOpaqueMVar ty' (← mvarId.getTag)
      mvarId.assign <| ← mkLetFVars (usedLetOnly := false) (fvarIds.map .fvar) g
      return ((fvarIds, givenNames'), g.mvarId!)

/--
Like `Lean.MVarId.extractLets` but extracts lets from a local declaration.
If the local declaration has a value, then both its type and value are modified.
-/
def Lean.MVarId.extractLetsLocalDecl (mvarId : MVarId) (fvarId : FVarId) (givenNames : List Name) (config : ExtractLetsConfig := {}) :
    MetaM ((Array FVarId × List Name) × MVarId) := do
  mvarId.checkNotAssigned `extract_lets
  mvarId.withReverted #[fvarId] fun mvarId fvars => mvarId.withContext do
    let finalize (fvarIds : Array FVarId) (givenNames' : List Name) (targetNew : Expr) := do
      let g ← mkFreshExprSyntheticOpaqueMVar targetNew (← mvarId.getTag)
      mvarId.assign <| ← mkLetFVars (usedLetOnly := false) (fvarIds.map .fvar) g
      return ((fvarIds, givenNames'), fvars.map .some, g.mvarId!)
    match ← mvarId.getType with
    | .forallE n t b i =>
      Meta.extractLets #[t] givenNames (config := config) fun fvarIds es givenNames' => do
        let t' := es[0]!
        if fvarIds.isEmpty && t == t' then
          throwMadeNoProgress `extract_lets mvarId
        finalize fvarIds givenNames' (.forallE n t' b i)
    | .letE n t v b ndep =>
      Meta.extractLets #[t, v] givenNames (config := config) fun fvarIds es givenNames' => do
        let t' := es[0]!
        let v' := es[1]!
        if fvarIds.isEmpty && t == t' && v == v' then
          throwMadeNoProgress `extract_lets mvarId
        finalize fvarIds givenNames' (.letE n t' v' b ndep)
    | _ => throwTacticEx `extract_lets mvarId "unexpected auxiliary target"

/--
Lifts `let` and `letFun` expressions in target as far out as possible.
Throws an exception if nothing is lifted.

Like `Lean.MVarId.extractLets`, but top-level lets are not added to the local context.
-/
def Lean.MVarId.liftLets (mvarId : MVarId) (config : LiftLetsConfig := {}) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `lift_lets
    let ty ← mvarId.getType
    let ty' ← Meta.liftLets ty (config := config)
    if ty == ty' then
      throwMadeNoProgress `lift_lets mvarId
    mvarId.replaceTargetDefEq ty'

/--
Like `Lean.MVarId.liftLets` but lifts lets in a local declaration.
If the local declaration has a value, then both its type and value are modified.
-/
def Lean.MVarId.liftLetsLocalDecl (mvarId : MVarId) (fvarId : FVarId) (config : LiftLetsConfig := {}) : MetaM MVarId := do
  mvarId.checkNotAssigned `lift_lets
  -- Revert to make sure the resulting type/value refers fvars that come after `fvarId`.
  -- (Note: reverting isn't necessary unless both `merge := true` and `useContext := true`.)
  Prod.snd <$> mvarId.withReverted #[fvarId] fun mvarId fvars => mvarId.withContext do
    let finalize (targetNew : Expr) := do
      return ((), fvars.map .some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n t b i =>
      let t' ← Meta.liftLets t (config := config)
      if t == t' then
        throwMadeNoProgress `lift_lets mvarId
      finalize (.forallE n t' b i)
    | .letE n t v b ndep =>
      let t' ← Meta.liftLets t (config := config)
      let v' ← Meta.liftLets v (config := config)
      if t == t' && v == v' then
        throwMadeNoProgress `lift_lets mvarId
      finalize (.letE n t' v' b ndep)
    | _ => throwTacticEx `lift_lets mvarId "unexpected auxiliary target"
