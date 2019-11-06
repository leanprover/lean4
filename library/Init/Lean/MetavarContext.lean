/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Control.Conditional
import Init.Data.Option
import Init.Data.List
import Init.Data.Nat
import Init.Lean.LocalContext
import Init.Lean.MonadCache
import Init.Lean.NameGenerator

namespace Lean

structure MetavarDecl :=
(userName  : Name := Name.anonymous)
(lctx      : LocalContext)
(type      : Expr)
(depth     : Nat)
(synthetic : Bool)

namespace MetavarDecl
instance : Inhabited MetavarDecl := ⟨{ lctx := arbitrary _, type := arbitrary _, depth := 0, synthetic := false }⟩
end MetavarDecl

structure DelayedMetavarAssignment :=
(lctx     : LocalContext)
(fvars    : Array Expr)
(val      : Expr)

structure MetavarContext :=
(depth       : Nat := 0)
(lDepth      : PersistentHashMap Name Nat := {})
(decls       : PersistentHashMap Name MetavarDecl := {})
(lAssignment : PersistentHashMap Name Level := {})
(eAssignment : PersistentHashMap Name Expr := {})
(dAssignment : PersistentHashMap Name DelayedMetavarAssignment := {})

namespace MetavarContext

instance : Inhabited MetavarContext := ⟨{}⟩

@[export lean_mk_metavar_ctx]
def mkMetavarContext : Unit → MetavarContext :=
fun _ => {}

/- Low level API for creating metavariable declarations.
   It is used to implement actions in the monads `Elab` and `Tactic`.
   It should not be used directly since the argument `(mvarId : Name)` is assumed to be "unique". -/
@[export lean_metavar_ctx_mk_decl]
def mkDecl (mctx : MetavarContext) (mvarId : Name) (userName : Name) (lctx : LocalContext) (type : Expr) (synthetic : Bool := false) : MetavarContext :=
{ decls := mctx.decls.insert mvarId {
    userName  := userName,
    lctx      := lctx,
    type      := type,
    depth     := mctx.depth,
    synthetic := synthetic },
  .. mctx }

@[export lean_metavar_ctx_find_decl]
def findDecl (m : MetavarContext) (mvarId : Name) : Option MetavarDecl :=
m.decls.find mvarId

def getDecl (m : MetavarContext) (mvarId : Name) : MetavarDecl :=
match m.decls.find mvarId with
| some decl => decl
| none      => panic! "unknown metavariable"

@[export lean_metavar_ctx_assign_level]
def assignLevel (m : MetavarContext) (mvarId : Name) (val : Level) : MetavarContext :=
{ lAssignment := m.lAssignment.insert mvarId val, .. m }

@[export lean_metavar_ctx_assign_expr]
def assignExpr (m : MetavarContext) (mvarId : Name) (val : Expr) : MetavarContext :=
{ eAssignment := m.eAssignment.insert mvarId val, .. m }

@[export lean_metavar_ctx_assign_delayed]
def assignDelayed (m : MetavarContext) (mvarId : Name) (lctx : LocalContext) (fvars : Array Expr) (val : Expr) : MetavarContext :=
{ dAssignment := m.dAssignment.insert mvarId { lctx := lctx, fvars := fvars, val := val }, .. m }

@[export lean_metavar_ctx_get_level_assignment]
def getLevelAssignment (m : MetavarContext) (mvarId : Name) : Option Level :=
m.lAssignment.find mvarId

@[export lean_metavar_ctx_get_expr_assignment]
def getExprAssignment (m : MetavarContext) (mvarId : Name) : Option Expr :=
m.eAssignment.find mvarId

@[export lean_metavar_ctx_get_delayed_assignment]
def getDelayedAssignment (m : MetavarContext) (mvarId : Name) : Option DelayedMetavarAssignment :=
m.dAssignment.find mvarId

@[export lean_metavar_ctx_is_level_assigned]
def isLevelAssigned (m : MetavarContext) (mvarId : Name) : Bool :=
m.lAssignment.contains mvarId

@[export lean_metavar_ctx_is_expr_assigned]
def isExprAssigned (m : MetavarContext) (mvarId : Name) : Bool :=
m.eAssignment.contains mvarId

@[export lean_metavar_ctx_is_delayed_assigned]
def isDelayedAssigned (m : MetavarContext) (mvarId : Name) : Bool :=
m.dAssignment.contains mvarId

@[export lean_metavar_ctx_erase_delayed]
def eraseDelayed (m : MetavarContext) (mvarId : Name) : MetavarContext :=
{ dAssignment := m.dAssignment.erase mvarId, .. m }

def isLevelAssignable (mctx : MetavarContext) (mvarId : Name) : Bool :=
match mctx.lDepth.find mvarId with
| some d => d == mctx.depth
| _      => panic! "unknown universe metavariable"

def isExprAssignable (mctx : MetavarContext) (mvarId : Name) : Bool :=
let decl := mctx.getDecl mvarId;
decl.depth == mctx.depth

/-- Return true iff the given level contains an assigned metavariable. -/
def hasAssignedLevelMVar (mctx : MetavarContext) : Level → Bool
| Level.succ lvl       => lvl.hasMVar && hasAssignedLevelMVar lvl
| Level.max lvl₁ lvl₂  => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.imax lvl₁ lvl₂ => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.mvar mvarId    => mctx.isLevelAssigned mvarId
| Level.zero           => false
| Level.param _        => false

/-- Return `true` iff expression contains assigned (level/expr) metavariables -/
def hasAssignedMVar (mctx : MetavarContext) : Expr → Bool
| Expr.const _ lvls    => lvls.any (hasAssignedLevelMVar mctx)
| Expr.sort lvl        => hasAssignedLevelMVar mctx lvl
| Expr.app f a         => (f.hasMVar && hasAssignedMVar f) || (a.hasMVar && hasAssignedMVar a)
| Expr.letE _ t v b    => (t.hasMVar && hasAssignedMVar t) || (v.hasMVar && hasAssignedMVar v) || (b.hasMVar && hasAssignedMVar b)
| Expr.forallE _ _ d b => (d.hasMVar && hasAssignedMVar d) || (b.hasMVar && hasAssignedMVar b)
| Expr.lam _ _ d b     => (d.hasMVar && hasAssignedMVar d) || (b.hasMVar && hasAssignedMVar b)
| Expr.fvar _          => false
| Expr.bvar _          => false
| Expr.lit _           => false
| Expr.mdata _ e       => e.hasMVar && hasAssignedMVar e
| Expr.proj _ _ e      => e.hasMVar && hasAssignedMVar e
| Expr.mvar mvarId     => mctx.isExprAssigned mvarId

/-- Return true iff the given level contains a metavariable that can be assigned. -/
def hasAssignableLevelMVar (mctx : MetavarContext) : Level → Bool
| Level.succ lvl       => lvl.hasMVar && hasAssignableLevelMVar lvl
| Level.max lvl₁ lvl₂  => (lvl₁.hasMVar && hasAssignableLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignableLevelMVar lvl₂)
| Level.imax lvl₁ lvl₂ => (lvl₁.hasMVar && hasAssignableLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignableLevelMVar lvl₂)
| Level.mvar mvarId    => mctx.isLevelAssignable mvarId
| Level.zero           => false
| Level.param _        => false

private partial def instantiateLevelMVarsAux : Level → StateM MetavarContext Level
| lvl@(Level.succ lvl₁)      => do lvl₁ ← instantiateLevelMVarsAux lvl₁; pure (Level.updateSucc! lvl lvl₁)
| lvl@(Level.max lvl₁ lvl₂)  => do lvl₁ ← instantiateLevelMVarsAux lvl₁; lvl₂ ← instantiateLevelMVarsAux lvl₂; pure (Level.updateMax! lvl lvl₁ lvl₂)
| lvl@(Level.imax lvl₁ lvl₂) => do lvl₁ ← instantiateLevelMVarsAux lvl₁; lvl₂ ← instantiateLevelMVarsAux lvl₂; pure (Level.updateIMax! lvl lvl₁ lvl₂)
| lvl@(Level.mvar mvarId)    => do
  mctx ← get;
  match getLevelAssignment mctx mvarId with
  | some newLvl =>
    if !newLvl.hasMVar then pure newLvl
    else do
      newLvl' ← instantiateLevelMVarsAux newLvl;
      modify $ fun mctx => mctx.assignLevel mvarId newLvl';
      pure newLvl'
  | none        => pure lvl
| lvl => pure lvl

namespace InstantiateExprMVars
private abbrev M := StateM (WithHashMapCache Expr Expr MetavarContext)

@[inline] private def instantiateLevelMVars (lvl : Level) : M Level :=
WithHashMapCache.fromState $ instantiateLevelMVarsAux lvl

@[inline] private def visit (f : Expr → M Expr) (e : Expr) : M Expr :=
if !e.hasMVar then pure e else checkCache e f

@[inline] private def getMCtx : M MetavarContext :=
do s ← get; pure s.state

@[inline] private def modifyCtx (f : MetavarContext → MetavarContext) : M Unit :=
modify $ fun s => { state := f s.state, .. s }

/--
  Auxiliary function for `instantiateDelayed`.
  `instantiateDelayed main lctx fvars i body` is used to create `fun fvars[0, i) => body`.
  It fails if one of variable declarations in `fvars` still contains unassigned metavariables.

  Pre: all expressions in `fvars` are `Expr.fvar`, and `lctx` contains their declarations. -/
@[specialize] private def instantiateDelayedAux (main : Expr → M Expr) (lctx : LocalContext) (fvars : Array Expr) : Nat → Expr → M (Option Expr)
| 0,   b => pure b
| i+1, b => do
  let fvar := fvars.get! i;
  match lctx.findFVar fvar with
  | none => panic! "unknown free variable"
  | some (LocalDecl.cdecl _ _ n ty bi)  => do
    ty ← visit main ty;
    if ty.hasMVar then pure none
    else instantiateDelayedAux i (Expr.lam n bi (ty.abstractRange i fvars) b)
  | some (LocalDecl.ldecl _ _ n ty val) => do
    ty  ← visit main ty;
    if ty.hasMVar then pure none
    else do
      val ← visit main val;
      if val.hasMVar then pure none
      else
        let ty  := ty.abstractRange i fvars;
        let val := val.abstractRange i fvars;
        instantiateDelayedAux i (Expr.letE n ty val b)

/-- Try to instantiate a delayed assignment. Return `none` (i.e., fail) if assignment still contains variables. -/
@[inline] private def instantiateDelayed (main : Expr → M Expr) (mvarId : Name) : DelayedMetavarAssignment → M (Option Expr)
| { lctx := lctx, fvars := fvars, val := val } => do
  newVal ← visit main val;
  let fail : M (Option Expr) := do {
     /- Join point for updating delayed assignment and failing -/
     modifyCtx $ fun mctx => assignDelayed mctx mvarId lctx fvars newVal;
     pure none
  };
  if newVal.hasMVar then fail
  else do
    /- Create `fun fvars => newVal`.
       It fails if there is a one of the variable declarations in `fvars` still contain metavariables. -/
    newE ← instantiateDelayedAux main lctx fvars fvars.size (newVal.abstract fvars);
    match newE with
    | none      => fail
    | some newE => do
      /- Succeeded. Thus, replace delayed assignment with a regular assignment. -/
      modifyCtx $ fun mctx => assignExpr (eraseDelayed mctx mvarId) mvarId newE;
      pure (some newE)

/-- instantiateExprMVars main function -/
partial def main : Expr → M Expr
| e@(Expr.proj _ _ s)      => do s ← visit main s; pure (e.updateProj! s)
| e@(Expr.forallE _ _ d b) => do d ← visit main d; b ← visit main b; pure (e.updateForallE! d b)
| e@(Expr.lam _ _ d b)     => do d ← visit main d; b ← visit main b; pure (e.updateLambdaE! d b)
| e@(Expr.letE _ t v b)    => do t ← visit main t; v ← visit main v; b ← visit main b; pure (e.updateLet! t v b)
| e@(Expr.const _ lvls)    => do lvls ← lvls.mapM instantiateLevelMVars; pure (e.updateConst! lvls)
| e@(Expr.sort lvl)        => do lvl ← instantiateLevelMVars lvl; pure (e.updateSort! lvl)
| e@(Expr.mdata _ b)       => do b ← visit main b; pure (e.updateMData! b)
| e@(Expr.app _ _)         => e.withAppRev $ fun f revArgs => do
  let wasMVar := f.isMVar;
  f ← visit main f;
  if wasMVar && f.isLambda then
    -- Some of the arguments in revArgs are irrelevant after we beta reduce.
    visit main (f.betaRev revArgs)
  else do
    revArgs ← revArgs.mapM (visit main);
    pure (mkAppRev f revArgs)
| e@(Expr.mvar mvarId)     => checkCache e $ fun e => do
  mctx ← getMCtx;
  match mctx.getExprAssignment mvarId with
  | some newE => do
    newE' ← visit main newE;
    modifyCtx $ fun mctx => mctx.assignExpr mvarId newE';
    pure newE'
  | none =>
    /- A delayed assignment can be transformed into a regular assignment
       as soon as all metavariables occurring in the assigned value have
       been assigned. -/
    match mctx.getDelayedAssignment mvarId with
    | some d => do
       newE ← instantiateDelayed main mvarId d;
       pure $ newE.getD e
    | none   => pure e
| e => pure e

end InstantiateExprMVars

def instantiateMVars (mctx : MetavarContext) (e : Expr) : Expr × MetavarContext :=
if !e.hasMVar then (e, mctx)
else (WithHashMapCache.toState $ InstantiateExprMVars.main e).run mctx

namespace DependsOn

private abbrev M := StateM ExprSet

@[inline] private def visit (main : Expr → M Bool) (e : Expr) : M Bool :=
if !e.hasMVar && !e.hasFVar then
  pure false
else do
  s ← get;
  if s.contains e then
    pure false
  else do
    modify $ fun s => s.insert e;
    main e

@[specialize] private partial def dep (mctx : MetavarContext) (p : Name → Bool) : Expr → M Bool
| e@(Expr.proj _ _ s)      => visit dep s
| e@(Expr.forallE _ _ d b) => visit dep d <||> visit dep b
| e@(Expr.lam _ _ d b)     => visit dep d <||> visit dep b
| e@(Expr.letE _ t v b)    => visit dep t <||> visit dep v <||> visit dep b
| e@(Expr.mdata _ b)       => visit dep b
| e@(Expr.app f a)         => visit dep a <||> if f.isApp then dep f else visit dep f
| e@(Expr.mvar mvarId)     =>
  match mctx.getExprAssignment mvarId with
  | some a => visit dep a
  | none   =>
    let lctx := (mctx.getDecl mvarId).lctx;
    pure $ lctx.any $ fun decl => p decl.name
| e@(Expr.fvar fvarId)     => pure $ p fvarId
| e                        => pure false

@[inline] partial def main (mctx : MetavarContext) (p : Name → Bool) (e : Expr) : M Bool :=
if !e.hasFVar && !e.hasMVar then pure false else dep mctx p e

end DependsOn

/--
  Return `true` iff `e` depends on a free variable `x` s.t. `p x` is `true`.
  For each metavariable `?m` occurring in `x`
  1- If `?m := t`, then we visit `t` looking for `x`
  2- If `?m` is unassigned, then we consider the worst case and check whether `x` is in the local context of `?m`.
     This case is a "may dependency". That is, we may assign a term `t` to `?m` s.t. `t` contains `x`. -/
@[inline] def exprDependsOn (mctx : MetavarContext) (p : Name → Bool) (e : Expr) : Bool :=
(DependsOn.main mctx p e).run' {}

/--
  Similar to `exprDependsOn`, but checks the expressions in the given local declaration
  depends on a free variable `x` s.t. `p x` is `true`. -/
@[inline] def localDeclDependsOn (mctx : MetavarContext) (p : Name → Bool) : LocalDecl → Bool
| LocalDecl.cdecl _ _ _ type _     => exprDependsOn mctx p type
| LocalDecl.ldecl _ _ _ type value => (DependsOn.main mctx p type <||> DependsOn.main mctx p value).run' {}

inductive MkBindingException
| revertFailure (lctx : LocalContext) (toRevert : Array Expr) (decl : LocalDecl)
| readOnlyMVar (mvarId : Name)
| mkAuxMVarNotSupported

namespace MkBindingException
def toStr : MkBindingException → String
| revertFailure lctx toRevert decl =>
  "failed to revert "
  ++ toString (toRevert.map (fun x => "'" ++ toString (lctx.findFVar x).get!.userName ++ "'"))
  ++ ", '" ++ toString decl.userName ++ "' depends on them, and it is an auxiliary declaration created by the elaborator"
  ++ " (possible solution: use tactic 'clear' to remove '" ++ toString decl.userName ++ "' from local context)"
| readOnlyMVar mvarId   => "failed to create binding due to read only metavariable " ++ toString mvarId
| mkAuxMVarNotSupported => "auxiliary metavariables are not supported"

instance : HasToString MkBindingException := ⟨toStr⟩
end MkBindingException

namespace MkBinding

/--
 `MkBinding` and `elimMVarDepsAux` are mutually recursive, but `cache` is only used at `elimMVarDepsAux`.
  We use a single state object for convenience.

  We have a `NameGenerator` because we need to generate fresh auxiliary metavariables.
-/
structure MkBindingState :=
(mctx  : MetavarContext)
(ngen  : NameGenerator)
(cache : HashMap Expr Expr := {}) --

private abbrev M := EStateM MkBindingException MkBindingState

instance : MonadHashMapCacheAdapter Expr Expr M :=
{ getCache    := do s ← get; pure s.cache,
  modifyCache := fun f => modify $ fun s => { cache := f s.cache, .. s } }

/-- Similar to `Expr.abstractRange`, but handles metavariables correctly.
    It uses `elimMVarDeps` to ensure `e` and the type of the free variables `xs` do not
    contain a metavariable `?m` s.t. local context of `?m` contains a free variable in `xs`.

    `elimMVarDeps` is defined later in this file. -/
@[inline] private def abstractRange (elimMVarDeps : Array Expr → Expr → M Expr) (lctx : LocalContext) (xs : Array Expr) (i : Nat) (e : Expr) : M Expr :=
do e ← elimMVarDeps xs e;
   pure (e.abstractRange i xs)

/-- Similar to `LocalContext.mkBinding`, but handles metavariables correctly. -/
@[specialize] def mkBinding (isLambda : Bool) (elimMVarDeps : Array Expr → Expr → M Expr)
                            (lctx : LocalContext) (xs : Array Expr) (e : Expr) : M Expr :=
do e ← abstractRange elimMVarDeps lctx xs xs.size e;
   xs.size.foldRevM
    (fun i e =>
      let x := xs.get! i;
      match lctx.findFVar x with
      | some (LocalDecl.cdecl _ _ n type bi) => do
        type ← abstractRange elimMVarDeps lctx xs i type;
        if isLambda then
          pure $ Expr.lam n bi type e
        else
          pure $ Expr.forallE n bi type e
      | some (LocalDecl.ldecl _ _ n type value) => do
        type  ← abstractRange elimMVarDeps lctx xs i type;
        value ← abstractRange elimMVarDeps lctx xs i value;
        pure $ Expr.letE n type value e
      | none => panic! "unknown free variable")
   e

@[inline] private def mkLambda (elimMVarDeps : Array Expr → Expr → M Expr) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : M Expr :=
mkBinding true elimMVarDeps lctx xs b

@[inline] private def mkForall (elimMVarDeps : Array Expr → Expr → M Expr) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : M Expr :=
mkBinding false elimMVarDeps lctx xs b

/-- Return the local declaration of the free variable `x` in `xs` with the smallest index -/
private def getLocalDeclWithSmallestIdx (lctx : LocalContext) (xs : Array Expr) : LocalDecl :=
let d : LocalDecl := (lctx.findFVar $ xs.get! 0).get!;
xs.foldlFrom
  (fun d x =>
    let decl := (lctx.findFVar x).get!;
    if decl.index < d.index then decl else d)
  d 1

/-- Given `toRevert` an array of free variables s.t. `lctx` contains their declarations,
    return a new array of free variables that contains `toRevert` and all free variables
    in `lctx` that may depend on `toRevert`.

    Remark: the result is sorted by `LocalDecl` indices. -/
private def collectDeps (mctx : MetavarContext) (lctx : LocalContext) (toRevert : Array Expr) : Except MkBindingException (Array Expr) :=
if toRevert.size == 0 then pure toRevert
else
  let minDecl := getLocalDeclWithSmallestIdx lctx toRevert;
  lctx.foldlFromM
    (fun newToRevert decl =>
      if toRevert.any (fun x => decl.name == x.fvarId!) then
        pure (newToRevert.push decl.toExpr)
      else if localDeclDependsOn mctx (fun fvarId => newToRevert.any $ fun x => x.fvarId! == fvarId) decl then
        if decl.binderInfo.isAuxDecl then
          throw (MkBindingException.revertFailure lctx toRevert decl)
        else
          pure (newToRevert.push decl.toExpr)
      else
        pure newToRevert)
    (Array.mkEmpty toRevert.size)
    minDecl

/-- Create a new `LocalContext` by removing the free variables in `toRevert` from `lctx`.
    We use this function when we create auxiliary metavariables at `elimMVarDepsAux`. -/
private def reduceLocalContext (lctx : LocalContext) (toRevert : Array Expr) : LocalContext :=
toRevert.foldr
  (fun x lctx => lctx.erase x.fvarId!)
  lctx

@[inline] private def visit (f : Expr → M Expr) (e : Expr) : M Expr :=
if !e.hasMVar then pure e else checkCache e f

@[inline] private def getMCtx : M MetavarContext :=
do s ← get; pure s.mctx

/-- Return free variables in `xs` that are in the local context `lctx` -/
private def getInScope (lctx : LocalContext) (xs : Array Expr) : Array Expr :=
xs.foldl
  (fun scope x =>
    if lctx.contains x.fvarId! then
      scope.push x
    else
      scope)
  #[]

/-- Execute `x` with an empty cache, and then restore the original cache. -/
@[inline] private def withFreshCache {α} (x : M α) : M α :=
do cache ← modifyGet $ fun s => (s.cache, { cache := {}, .. s });
   a ← x;
   modify $ fun s => { cache := cache, .. s };
   pure a

@[inline] private def mkForallAux (elimMVarDepsAux : Array Expr → Expr → M Expr) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : M Expr :=
mkForall
  (fun xs e =>
    if !e.hasMVar then
      pure e
    else
      -- The cached results at `elimMVarDepsAux` depend on `xs`. So, we must reset the cache.
      withFreshCache $ elimMVarDepsAux xs e)
  lctx xs b

/-- Create an application `mvar ys` where `ys` are the free variables `xs` which are not let-declarations.
    All free variables in `xs` are in the context `lctx`. -/
private def mkMVarApp (lctx : LocalContext) (mvar : Expr) (xs : Array Expr) : Expr :=
xs.foldl (fun e x => if (lctx.findFVar x).get!.isLet then e else Expr.app e x) mvar

private def mkAuxMVar (lctx : LocalContext) (type : Expr) (synthetic : Bool) : M Name :=
do s ← get;
   let mvarId := s.ngen.curr;
   modify $ fun s => { mctx := s.mctx.mkDecl mvarId Name.anonymous lctx type synthetic, ngen := s.ngen.next, .. s };
   pure mvarId

private partial def elimMVarDepsAux : Array Expr → Expr → M Expr
| xs, e@(Expr.proj _ _ s)      => do s ← visit (elimMVarDepsAux xs) s; pure (e.updateProj! s)
| xs, e@(Expr.forallE _ _ d b) => do d ← visit (elimMVarDepsAux xs) d; b ← visit (elimMVarDepsAux xs) b; pure (e.updateForallE! d b)
| xs, e@(Expr.lam _ _ d b)     => do d ← visit (elimMVarDepsAux xs) d; b ← visit (elimMVarDepsAux xs) b; pure (e.updateLambdaE! d b)
| xs, e@(Expr.letE _ t v b)    => do t ← visit (elimMVarDepsAux xs) t; v ← visit (elimMVarDepsAux xs) v; b ← visit (elimMVarDepsAux xs) b; pure (e.updateLet! t v b)
| xs, e@(Expr.mdata _ b)       => do b ← visit (elimMVarDepsAux xs) b; pure (e.updateMData! b)
| xs, e@(Expr.app _ _)         => e.withAppRev $ fun f revArgs => do
  f ← visit (elimMVarDepsAux xs) f;
  revArgs ← revArgs.mapM (visit (elimMVarDepsAux xs));
  pure (mkAppRev f revArgs)
| xs, e@(Expr.mvar mvarId) => do
  mctx ← getMCtx;
  match mctx.getExprAssignment mvarId with
  | some a => visit (elimMVarDepsAux xs) a
  | none   =>
    let mvarDecl := mctx.getDecl mvarId;
    let mvarLCtx := mvarDecl.lctx;
    let toRevert := getInScope mvarLCtx xs;
    if toRevert.size == 0 then
      pure e
    else if !mctx.isExprAssignable mvarId then
      throw $ MkBindingException.readOnlyMVar mvarId
    else
      match collectDeps mctx mvarLCtx toRevert with
      | Except.error ex    => throw ex
      | Except.ok toRevert => do
        let newMVarLCtx   := reduceLocalContext mvarLCtx toRevert;
        newMVarType ← mkForallAux (fun xs e => elimMVarDepsAux xs e) mvarLCtx toRevert mvarDecl.type;
        newMVarId   ← mkAuxMVar newMVarLCtx newMVarType mvarDecl.synthetic;
        let newMVar := Expr.mvar newMVarId;
        let result  := mkMVarApp mvarLCtx newMVar toRevert;
        if mvarDecl.synthetic then
          modify (fun s => { mctx := assignDelayed s.mctx newMVarId mvarLCtx toRevert e, .. s })
        else
          modify (fun s => { mctx := assignExpr s.mctx mvarId result, .. s });
        pure result
| xs, e => pure e

partial def elimMVarDeps (xs : Array Expr) (e : Expr) : M Expr :=
if !e.hasMVar then
  pure e
else
  withFreshCache $ elimMVarDepsAux xs e

end MkBinding

def mkBinding (isLambda : Bool) (mctx : MetavarContext) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr)
    : Except MkBindingException (MetavarContext × NameGenerator × Expr) :=
match (MkBinding.mkBinding isLambda MkBinding.elimMVarDeps lctx xs e).run { mctx := mctx, ngen := ngen } with
| EStateM.Result.ok e s      => Except.ok (s.mctx, s.ngen, e)
| EStateM.Result.error err _ => Except.error err

@[inline] def mkLambda (mctx : MetavarContext) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr)
    : Except MkBindingException (MetavarContext × NameGenerator × Expr) :=
mkBinding true mctx ngen lctx xs e

@[inline] def mkForall (mctx : MetavarContext) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr)
    : Except MkBindingException (MetavarContext × NameGenerator × Expr) :=
mkBinding false mctx ngen lctx xs e

end MetavarContext
end Lean
