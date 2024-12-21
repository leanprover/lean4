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
-/

namespace ExtractLets

def containsLet (e : Expr) : Bool :=
  Option.isSome <| e.find? fun e' => e'.isLet || e'.isConstOf ``letFun

structure LocalDecl' where
  decl : LocalDecl
  /--
  If true, is a `let`, if false, is a `letFun`.
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

abbrev M := ReaderT ExtractLetsConfig <| MonadCacheT ExprStructEq Expr <| StateRefT State MetaM

/-- Gets the next name to use for extracted `let`s -/
def nextName? : M (Option Name) := do
  let s ← get
  match s.givenNames, (← read).onlyGivenNames with
  | n :: ns, _      => set { s with givenNames := ns }; return n
  | []     , true   => return none
  | []     , false  => return `_

def extractable (fvars : List Expr) (e : Expr) : Bool :=
  !e.hasAnyFVar (fvars.contains <| .fvar ·)

def nextNameForBinderName? (binderName : Name) : M (Option Name) := do
  if let some n ← nextName? then
    if n == `_ then
      let binderName := if binderName.isAnonymous then `a else binderName
      mkFreshUserName binderName
    else
      return n
  else
    return none

/--
Returns
-/
def isExtractableLet (fvars : List Expr) (n : Name) (t v : Expr) : M (Bool × Name) := do
  if extractable fvars t && extractable fvars v then
    if let some n ← nextNameForBinderName? n then
      return (true, n)
  -- In lift mode, we temporarily extract non-extractable lets, but we do not make use of the givenNames for them.
  if (← read).lift then
    return (true, n)
  return (false, n)

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

def withEnsuringDeclsInContext [Monad m] [MonadControlT MetaM m] [MonadLCtx m] (decls : Array LocalDecl') (k : m α) : m α := do
  let lctx ← getLCtx
  let decls := decls |>.filter (!lctx.contains ·.decl.fvarId) |>.map (·.decl)
  withExistingLocalDecls decls.toList k

def mkLetDecls (decls : Array LocalDecl') (e : Expr) : MetaM Expr := do
  withEnsuringDeclsInContext decls do
    decls.foldrM (init := e) fun { decl, isLet } e => do
      if isLet then
        return .letE decl.userName decl.type decl.value (e.abstract #[decl.toExpr]) false
      else
        let n := decl.userName
        let x := decl.toExpr
        let α := decl.type
        let ety ← inferType e
        let β := Expr.lam n α (ety.abstract #[x]) .default
        let v := decl.value
        let f := Expr.lam n α (e.abstract #[x]) .default
        let u1 ← getLevel α
        let u2 ← getLevel ety
        return mkAppN (.const ``letFun [u1, u2]) #[α, β, v, f]

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
Makes sure the declaration for `fvarId` is marked with `isLet := true`.
Used in `lift` mode to ensure that after merging, if any version was a `let`, it's a `let` rather than a `letFun`.
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

If `fvarId` is not among the `decls`, we assume it's a pre-existing declaration.

Used for `merge` feature.
-/
def withDeclInContext (fvarId : FVarId) (k : M α) : M α := do
  let decls := (← get).decls
  if let some idx := decls.findIdx? (·.decl.fvarId == fvarId) then
    withEnsuringDeclsInContext decls[0:idx+1] k
  else
    k

/--
Initializes the `valueMap` with all the local definitions that aren't implementation details.
-/
def initializeValueMap : M Unit := do
  let lctx ← getLCtx
  lctx.forM fun decl => do
    if decl.isLet && !decl.isImplementationDetail then
      let value ← instantiateMVars decl.value
      modify fun s => { s with valueMap := s.valueMap.insert value decl.fvarId }

/--
Extracts lets from `e`.
- `fvars` is an array of all the local variables from going under binders,
  used to detect whether an expression is extractable. Extracted `let`s do not have their fvarids in this list.
  This is not part of the cache key since it's an optimization and in principle derivable.
- `topLevel` is whether we are still looking at the top-level expression.
  The body of an extracted top-level let is also top-level.
  This is part of the cache key since it affects what is extracted.

Note: the return value may refer to fvars that are not in the current local context, but they are in the `decls` list.

Does not handle `descend := false`. See `Lean.Meta.ExtractLets.extractNoDescend`.
-/
partial def extractCore (fvars : List Expr) (e : Expr) (topLevel : Bool := false) : M Expr := do
  let cfg ← read
  if e.isAtomic then
    return e
  else
    checkCache (e : ExprStructEq) fun _ => do
      if !containsLet e then
        return e
      -- Don't check for proofs or types for top-level lets, since it's confusing not having them be extracted.
      if !(topLevel && (e.isLet || e.isLetFun || e.isMData)) then
        if !cfg.proofs then
          if ← isProof e then
            return e
        if !cfg.types then
          if ← isType e then
            return e
      match e with
      | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => unreachable!
      | .mdata _ e'      => return e.updateMData! (← extractCore fvars e' (topLevel := topLevel))
      | .proj _ _ s      => return e.updateProj! (← extractCore fvars s)
      | .app ..          => extractApp e
      | .letE n t v b _  => extractLetLike true n t v b (fun t v b => pure <| e.updateLet! t v b) (topLevel := topLevel)
      | .lam n t b i     => extractBinder n t b i (fun t b => e.updateLambda! i t b)
      | .forallE n t b i => extractBinder n t b i (fun t b => e.updateForall! i t b)
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
    if cfg.usedOnly && !b.hasLooseBVars then
      return ← extractCore fvars b (topLevel := topLevel)
    let t ← extractCore fvars t
    let v ← extractCore fvars v
    if cfg.merge then
      if let some fvarId := (← get).valueMap.get? v then
        if isLet && cfg.lift then ensureIsLet fvarId
        return ← withDeclInContext fvarId <|
          extractCore fvars (b.instantiate1 (.fvar fvarId)) (topLevel := topLevel)
    let (extract, n) ← isExtractableLet fvars n t v
    if !extract && !cfg.underBinder then
      return ← mk t v b
    withLetDecl n t v fun x => do
      if extract then
        addDecl (← x.fvarId!.getDecl) isLet
        extractCore fvars (b.instantiate1 x) (topLevel := topLevel)
      else
        let b ← extractCore (x :: fvars) (b.instantiate1 x)
        mk t v (b.abstract #[x])
  extractApp (e : Expr) : M Expr := do
    let cfg ← read
    -- The head and arguments of the application, pre-extraction
    let mut f := e.getAppFn
    let mut args := e.getAppArgs
    -- The head of the application, post-extraction
    let f' ←
      if f.isConstOf ``letFun && 4 ≤ args.size then
        let letF := mkAppN f args[0:4]
        let (n, t, v, b) := letF.letFun?.get!
        let f' ← extractLetLike false n t v b (topLevel := topLevel && args.size = 4)
          (fun t v b =>
            -- Strategy: construct letFun directly rather than use `mkLetFun`.
            -- We don't update the `β` argument.
            return mkApp4 f t args[1]! v (.lam n t b .default))
        f := letF
        args := args[4:]
        pure f'
      else
        extractCore fvars f
    if cfg.implicits then
      args ← args.mapM (extractCore fvars)
    else
      let mut fty ← inferType f
      let mut j := 0
      for i in [0:args.size] do
        unless fty.isForall do
          fty ← withTransparency .all <| whnf (fty.instantiateRevRange j i args)
          j := i
        let .forallE _ _ fty' bi := fty
          | throwError "Lean.Meta.ExtractLets.extractCore: expecting function, type is{indentD fty}"
        fty := fty'
        if bi.isExplicit then
          args := args.set! i <| ← extractCore fvars (args[i]!)
    return mkAppN f' args

/--
Extraction routine in the case `descend := false`.
It is easier to reason about `extractCore` and `extractNoDescend` if they are separate like this.
-/
partial def extractNoDescend (e : Expr) : M Expr := do
  -- We don't check for proofs or types for top-level lets, since it's confusing not having them be extracted.
  match e with
  | .mdata _ e'      => return e.updateMData! (← extractNoDescend e')
  | .letE n t v b _  => extractLetLike e n t v b
  | .app ..          =>
    if let some (n, t, v, b) := e.letFun? then
      extractLetLike e n t v b
    else
      return e
  | e                => return e
where
  extractLetLike (e : Expr) (n : Name) (t v b : Expr) : M Expr := do
    let cfg ← read
    if cfg.usedOnly && !b.hasLooseBVars then
      return ← extractNoDescend b
    if cfg.merge then
      if let some fvarId := (← get).valueMap.get? v then
        return ← withDeclInContext fvarId <|
          extractNoDescend (b.instantiate1 (.fvar fvarId))
    if let some n ← nextNameForBinderName? n then
      withLetDecl n t v fun x => do
        -- The `isLet` value doesn't matter in `descend := false` mode.
        addDecl (← x.fvarId!.getDecl) (isLet := true)
        extractNoDescend (b.instantiate1 x)
    else
      return e

def extractTopLevel (e : Expr) : M Expr := do
  let e ← instantiateMVars e
  let cfg ← read
  if cfg.descend then
    extractCore [] e (topLevel := true)
  else
    extractNoDescend e

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
  and with the post-extraction expressions.
-/
private def extractLetsImp (es : Array Expr) (givenNames : List Name) (k : Array FVarId → Array Expr → MetaM α) (config : ExtractLetsConfig) :
    MetaM α := do
  let (es, st) ← ExtractLets.extract es |>.run config |>.run' {} |>.run { givenNames }
  let decls := st.decls.map (·.decl)
  withExistingLocalDecls decls.toList (k (decls.map (·.fvarId)) es)

/--
Extracts `let` and `letFun` expressions into local definitions,
evaluating `k` at the post-extracted expressions and the extracted fvarids, within a context containing those local declarations.
- The `givenNames` is a list of explicit names to use for extracted local declarations.
  If a name is `_` (or if there is no provided given name and `config.onlyGivenNames` is true) then uses a hygienic name
  based on the existing binder name.
-/
def extractLets [Monad m] [MonadControlT MetaM m] (es : Array Expr) (givenNames : List Name) (k : Array FVarId → Array Expr → m α) (config : ExtractLetsConfig := {}) :
    m α :=
  map2MetaM (fun k => extractLetsImp es givenNames k config) k

end Lean.Meta

/--
Extracts `let` and `letFun` expressions from the target,
returning `FVarId`s for the extracted let declarations along with the new goal.
- The `givenNames` is a list of explicit names to use for extracted local declarations.
  If a name is `_` (or if there is no provided given name and `config.onlyGivenNames` is true) then uses a hygienic name
  based on the existing binder name.
-/
def Lean.MVarId.extractLets (mvarId : MVarId) (givenNames : List Name) (config : ExtractLetsConfig := {}) :
    MetaM (Array FVarId × MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `extract_lets
    let ty ← mvarId.getType
    Meta.extractLets #[ty] givenNames (config := config) fun fvarIds es => do
      let ty' := es[0]!
      if fvarIds.isEmpty && ty == ty' then
        throwTacticEx `extract_lets mvarId m!"nothing to extract"
      let g ← mkFreshExprSyntheticOpaqueMVar ty' (← mvarId.getTag)
      mvarId.assign <| ← mkLetFVars (usedLetOnly := false) (fvarIds.map .fvar) g
      return (fvarIds, g.mvarId!)

/--
Like `Lean.MVarId.extractLets` but extracts lets from a local declaration.
If the local declaration has a value, then both its type and value are modified.
-/
def Lean.MVarId.extractLetsLocalDecl (mvarId : MVarId) (fvarId : FVarId) (givenNames : List Name) (config : ExtractLetsConfig := {}) :
    MetaM (Array FVarId × MVarId) := do
  mvarId.checkNotAssigned `extract_lets
  mvarId.withReverted #[fvarId] fun mvarId fvars => mvarId.withContext do
    let finalize (fvarIds : Array FVarId) (targetNew : Expr) := do
      let g ← mkFreshExprSyntheticOpaqueMVar targetNew (← mvarId.getTag)
      mvarId.assign <| ← mkLetFVars (usedLetOnly := false) (fvarIds.map .fvar) g
      return (fvarIds, fvars.map .some, g.mvarId!)
    match ← mvarId.getType with
    | .forallE n t b i =>
      Meta.extractLets #[t] givenNames (config := config) fun fvarIds es => do
        let t' := es[0]!
        if fvarIds.isEmpty && t == t' then
          throwTacticEx `extract_lets mvarId m!"nothing to extract"
        finalize fvarIds (.forallE n t' b i)
    | .letE n t v b ndep =>
      Meta.extractLets #[t, v] givenNames (config := config) fun fvarIds es => do
        let t' := es[0]!
        let v' := es[1]!
        if fvarIds.isEmpty && t == t' && v == v' then
          throwTacticEx `extract_lets mvarId m!"nothing to extract"
        finalize fvarIds (.letE n t' v' b ndep)
    | _ => throwTacticEx `extract_lets mvarId "unexpected auxiliary target"
