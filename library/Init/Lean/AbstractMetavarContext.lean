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

/-
- We have two kinds of metavariables in Lean: regular and temporary.

- We use temporary metavariables during type class resolution,
  matching the left-hand side of equations, etc.

- During type class resolution and simplifier,
  we use temporary metavariables which are cheaper to create and
  dispose. Moreover, given a particular task using temporary
  metavariables (e.g., matching the left-hand side of an equation),
  we assume all metavariables share the same local context.

- Each regular metavariable has a unique id, a user-facing name, a
  local context, and a type. The term assigned to a metavariable must
  only contain free variables in the local context.

- A regular metavariable may be marked a synthetic. Synthetic
  metavariables cannot be assigned by the unifier. The tactic
  framework and elaborator are some of the modules responsible for
  assigning synthetic metavariables.

- When creating lambda/forall expressions, we need to convert/abstract
  free variables and convert them to bound variables. Now, suppose we
  a trying to create a lambda/forall expression by abstracting free
  variables `xs` and a term `t[?m]` which contains a metavariable
  `?m`, and the local context of `?m` contains `xs`. The term
  `fun xs => t[?m]` will be ill-formed if we later assign a term `s` to `?m`,
  and `s` contains free variables in `xs`. We address this issue by changing the free
  variable abstraction procedure. We consider two cases: `?m` is not
  synthetic, `?m` is synthetic. Assume the type of `?m` is `A`. Then,
  in both cases we create an auxiliary metavariable `?n` with type
  `forall xs => A`, and local context := local context of `?m` - `xs`.
  In both cases, we produce the term `fun xs => t[?n xs]`

  1- If `?m` is not synthetic, then we assign `?m := ?n xs`, and we produce the term
     `fun xs => t[?n xs]`

  2- If `?m` is synthetic, then we mark `?n` as a synthetic variable. However,
     `?n` is managed by the metavariable context itself.
     We say we have a "delayed assignment" `?n xs := ?m`
     That is, after a term `s` is assigned to `?m`, and `s` does not
     contain metavariables, we assign `fun xs => s` to `?n`.

Gruesome details

- When we create the type `forall xs => A` for `?n`, we may encounter
  the same issue if `A` contains metavariables. So, the process above
  is recursive. We claim it terminates because we keep creating new
  metavariables with smaller local contexts.

- The type of variables `xs` may contain metavariables, and we must
  recursively apply the process above. Again, we claim the process
  terminates because the metavariables is ocurring in the types of
  `xs`, they must have smaller local contexts.

- We can only assign `fun xs => s` to `?n` in case 2, the types
  of `xs` must also not contain metavariables. To be precise, it is
  sufficient they do not contain metavariables with local contexts
  containing any of the `xs`s.
-/

namespace Lean

structure MetavarDecl :=
(userName  : Name)
(lctx      : LocalContext)
(type      : Expr)
(synthetic : Bool)

namespace MetavarDecl

instance : Inhabited MetavarDecl :=
⟨⟨default _, default _, default _, false⟩⟩

end MetavarDecl

/--
  A delayed assignment for a metavariable `?m`. It represents an assignment of the form
  `?m := (fun fvars => val)`. The local context `lctx` provides the declarations for `fvars`.
  Note that `fvars` may not be defined in the local context for `?m`. -/
structure DelayedMetavarAssignment :=
(lctx     : LocalContext)
(fvars    : Array Expr)
(val      : Expr)

/--
  Abstract interface for metavariable context objects.  The
  `MetavarContext` is the main implementation and is used in the
  elaborator and tactic framework.
  The `TemporaryMetavariableContext` is used to implement the
  type class resolution procedures and matching for rewriting rules.  -/
class AbstractMetavarContext (σ : Type) :=
(empty                : σ)
(isReadOnlyLevelMVar  (mctx : σ) (mvarId : Name) : Bool)
(getLevelAssignment   (mctx : σ) (mvarId : Name) : Option Level)
(assignLevel          (mctx : σ) (mvarId : Name) (val : Level) : σ)
(isReadOnlyExprMVar   (mctx : σ) (mvarId : Name) : Bool)
(getExprAssignment    (mctx : σ) (mvarId : Name) : Option Expr)
(assignExpr           (mctx : σ) (mvarId : Name) (val : Expr) : σ)
(getDecl              (mctx : σ) (mvarId : Name) : MetavarDecl)
(assignDelayed        (mctx : σ) (mvarId : Name) (lctx : LocalContext) (fvars : Array Expr) (val : Expr) : σ)
(getDelayedAssignment (mctx : σ) (mvarId : Name) : Option DelayedMetavarAssignment)
(eraseDelayed         (mctx : σ) (mvarId : Name) : σ)
/- Supports auxiliary metavariables -/
(auxMVarSupport       : Bool)
/- Return `none` in case of failure, or if implementation does not support the creation of auxiliary metavariables. -/
(mkAuxMVar            (mctx : σ) (mvarId : Name) (lctx : LocalContext) (type : Expr) (synthetic : Bool) : σ)

namespace AbstractMetavarContext

variables {σ : Type} [AbstractMetavarContext σ]

@[inline] def isLevelAssigned (mctx : σ) (mvarId : Name) : Bool :=
(getLevelAssignment mctx mvarId).isSome

@[inline] def isExprAssigned (mctx : σ) (mvarId : Name) : Bool :=
(getExprAssignment mctx mvarId).isSome

/-- Return true iff the given level contains a non-readonly metavariable. -/
def hasAssignableLevelMVar (mctx : σ) : Level → Bool
| Level.succ lvl       => lvl.hasMVar && hasAssignableLevelMVar lvl
| Level.max lvl₁ lvl₂  => (lvl₁.hasMVar && hasAssignableLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignableLevelMVar lvl₂)
| Level.imax lvl₁ lvl₂ => (lvl₁.hasMVar && hasAssignableLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignableLevelMVar lvl₂)
| Level.mvar mvarId    => !isReadOnlyLevelMVar mctx mvarId
| Level.zero           => false
| Level.param _        => false

/-- Return true iff the given level contains an assigned metavariable. -/
def hasAssignedLevelMVar (mctx : σ) : Level → Bool
| Level.succ lvl       => lvl.hasMVar && hasAssignedLevelMVar lvl
| Level.max lvl₁ lvl₂  => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.imax lvl₁ lvl₂ => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.mvar mvarId    => isLevelAssigned mctx mvarId
| Level.zero           => false
| Level.param _        => false

/-- Return `true` iff expression contains assigned (level/expr) metavariables -/
def hasAssignedMVar (mctx : σ) : Expr → Bool
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
| Expr.mvar mvarId     => isExprAssigned mctx mvarId

partial def instantiateLevelMVars : Level → State σ Level
| lvl@(Level.succ lvl₁)      => do lvl₁ ← instantiateLevelMVars lvl₁; pure (Level.updateSucc! lvl lvl₁)
| lvl@(Level.max lvl₁ lvl₂)  => do lvl₁ ← instantiateLevelMVars lvl₁; lvl₂ ← instantiateLevelMVars lvl₂; pure (Level.updateMax! lvl lvl₁ lvl₂)
| lvl@(Level.imax lvl₁ lvl₂) => do lvl₁ ← instantiateLevelMVars lvl₁; lvl₂ ← instantiateLevelMVars lvl₂; pure (Level.updateIMax! lvl lvl₁ lvl₂)
| lvl@(Level.mvar mvarId)    => do
  mctx ← get;
  match getLevelAssignment mctx mvarId with
  | some newLvl =>
    if !newLvl.hasMVar then pure newLvl
    else do
      newLvl' ← instantiateLevelMVars newLvl;
      modify $ fun mctx => assignLevel mctx mvarId newLvl';
      pure newLvl'
  | none        => pure lvl
| lvl => pure lvl

namespace InstantiateExprMVars
abbrev M (σ : Type) := State (WithHashMapCache Expr Expr σ)

@[inline] def instantiateLevelMVars (lvl : Level) : M σ Level :=
WithHashMapCache.fromState $ AbstractMetavarContext.instantiateLevelMVars lvl

@[inline] def visit (f : Expr → M σ Expr) (e : Expr) : M σ Expr :=
if !e.hasMVar then pure e else checkCache e f

@[inline] def getMCtx : M σ σ :=
do s ← get; pure s.state

@[inline] def modifyCtx (f : σ → σ) : M σ Unit :=
modify $ fun s => { state := f s.state, .. s }

/--
  Auxiliary function for `instantiateDelayed`.
  `instantiateDelayed main lctx fvars i body` is used to create `fun fvars[0, i) => body`.
  It fails if one of variable declarations in `fvars` still contains unassigned metavariables.

  Pre: all expressions in `fvars` are `Expr.fvar`, and `lctx` contains their declarations. -/
@[specialize] def instantiateDelayedAux (main : Expr → M σ Expr) (lctx : LocalContext) (fvars : Array Expr) : Nat → Expr → M σ (Option Expr)
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
@[inline] def instantiateDelayed (main : Expr → M σ Expr) (mvarId : Name) : DelayedMetavarAssignment → M σ (Option Expr)
| { lctx := lctx, fvars := fvars, val := val } => do
  newVal ← visit main val;
  let fail : M σ (Option Expr) := do {
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
partial def main : Expr → M σ Expr
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
  match getExprAssignment mctx mvarId with
  | some newE => do
    newE' ← visit main newE;
    modifyCtx $ fun mctx => assignExpr mctx mvarId newE';
    pure newE'
  | none =>
    /- A delayed assignment can be transformed into a regular assignment
       as soon as all metavariables occurring in the assigned value have
       been assigned. -/
    match getDelayedAssignment mctx mvarId with
    | some d => do
       newE ← instantiateDelayed main mvarId d;
       pure $ newE.getD e
    | none   => pure e
| e => pure e

end InstantiateExprMVars

def instantiateMVars (e : Expr) : State σ Expr :=
if !e.hasMVar then pure e
else WithHashMapCache.toState $ InstantiateExprMVars.main e

namespace DependsOn

abbrev M := State ExprSet

@[inline] def visit (main : Expr → M Bool) (e : Expr) : M Bool :=
if !e.hasMVar && !e.hasFVar then
  pure false
else do
  s ← get;
  if s.contains e then
    pure false
  else do
    modify $ fun s => s.insert e;
    main e

@[specialize] partial def dep (mctx : σ) (p : Name → Bool) : Expr → M Bool
| e@(Expr.proj _ _ s)      => visit dep s
| e@(Expr.forallE _ _ d b) => visit dep d <||> visit dep b
| e@(Expr.lam _ _ d b)     => visit dep d <||> visit dep b
| e@(Expr.letE _ t v b)    => visit dep t <||> visit dep v <||> visit dep b
| e@(Expr.mdata _ b)       => visit dep b
| e@(Expr.app f a)         => visit dep a <||> if f.isApp then dep f else visit dep f
| e@(Expr.mvar mvarId)     =>
  match getExprAssignment mctx mvarId with
  | some a => visit dep a
  | none   =>
    let lctx := (getDecl mctx mvarId).lctx;
    pure $ lctx.any $ fun decl => p decl.name
| e@(Expr.fvar fvarId)     => pure $ p fvarId
| e                        => pure false

@[inline] partial def main (mctx : σ) (p : Name → Bool) (e : Expr) : M Bool :=
if !e.hasFVar && !e.hasMVar then pure false else dep mctx p e

end DependsOn

/--
  Return `true` iff `e` depends on a free variable `x` s.t. `p x` is `true`.
  For each metavariable `?m` occurring in `x`
  1- If `?m := t`, then we visit `t` looking for `x`
  2- If `?m` is unassigned, then we consider the worst case and check whether `x` is in the local context of `?m`.
     This case is a "may dependency". That is, we may assign a term `t` to `?m` s.t. `t` contains `x`. -/
@[inline] def exprDependsOn (mctx : σ) (p : Name → Bool) (e : Expr) : Bool :=
(DependsOn.main mctx p e).run' {}

/--
  Similar to `exprDependsOn`, but checks the expressions in the given local declaration
  depends on a free variable `x` s.t. `p x` is `true`. -/
@[inline] def localDeclDependsOn (mctx : σ) (p : Name → Bool) : LocalDecl → Bool
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
| readOnlyMVar _  => "failed to create binding due to read only metavariable"
| mkAuxMVarNotSupported => "auxiliary metavariables are not supported"

instance : HasToString MkBindingException := ⟨toStr⟩
end MkBindingException

namespace MkBinding

/--
 `MkBinding` and `elimMVarDepsAux` are mutually recursive, but `cache` is only used at `elimMVarDepsAux`.
  We use a single state object for convenience.

  We have a `NameGenerator` because we need to generate fresh auxiliary metavariables.
-/
structure MkBindingState (σ : Type) :=
(mctx  : σ)
(ngen  : NameGenerator)
(cache : HashMap Expr Expr := {}) --

abbrev M (σ : Type) := EState MkBindingException (MkBindingState σ)

instance (σ) : MonadHashMapCacheAdapter Expr Expr (M σ) :=
{ getCache    := do s ← get; pure s.cache,
  modifyCache := fun f => modify $ fun s => { cache := f s.cache, .. s } }

/-- Similar to `Expr.abstractRange`, but handles metavariables correctly.
    It uses `elimMVarDeps` to ensure `e` and the type of the free variables `xs` do not
    contain a metavariable `?m` s.t. local context of `?m` contains a free variable in `xs`.

    `elimMVarDeps` is defined later in this file. -/
@[inline] def abstractRange (elimMVarDeps : Array Expr → Expr → M σ Expr) (lctx : LocalContext) (xs : Array Expr) (i : Nat) (e : Expr) : M σ Expr :=
do e ← elimMVarDeps xs e;
   pure (e.abstractRange i xs)

/-- Similar to `LocalContext.mkBinding`, but handles metavariables correctly. -/
@[specialize] def mkBinding (isLambda : Bool) (elimMVarDeps : Array Expr → Expr → M σ Expr)
                            (lctx : LocalContext) (xs : Array Expr) (e : Expr) : M σ Expr :=
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

@[inline] def mkLambda (elimMVarDeps : Array Expr → Expr → M σ Expr) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : M σ Expr :=
mkBinding true elimMVarDeps lctx xs b

@[inline] def mkForall (elimMVarDeps : Array Expr → Expr → M σ Expr) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : M σ Expr :=
mkBinding false elimMVarDeps lctx xs b

/-- Return the local declaration of the free variable `x` in `xs` with the smallest index -/
def getLocalDeclWithSmallestIdx (lctx : LocalContext) (xs : Array Expr) : LocalDecl :=
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
def collectDeps (mctx : σ) (lctx : LocalContext) (toRevert : Array Expr) : Except MkBindingException (Array Expr) :=
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
def reduceLocalContext (lctx : LocalContext) (toRevert : Array Expr) : LocalContext :=
toRevert.foldr
  (fun x lctx => lctx.erase x.fvarId!)
  lctx

@[inline] def visit (f : Expr → M σ Expr) (e : Expr) : M σ Expr :=
if !e.hasMVar then pure e else checkCache e f

@[inline] def getMCtx : M σ σ :=
do s ← get; pure s.mctx

@[inline] def mkFreshId : M σ Name :=
modifyGet $ fun s => (s.ngen.curr, { ngen := s.ngen.next, .. s})

/-- Return free variables in `xs` that are in the local context `lctx` -/
def getInScope (lctx : LocalContext) (xs : Array Expr) : Array Expr :=
xs.foldl
  (fun scope x =>
    if lctx.contains x.fvarId! then
      scope.push x
    else
      scope)
  #[]

/-- Execute `x` with an empty cache, and then restore the original cache. -/
@[inline] def withFreshCache {α} (x : M σ α) : M σ α :=
do cache ← modifyGet $ fun s => (s.cache, { cache := {}, .. s });
   a ← x;
   modify $ fun s => { cache := cache, .. s };
   pure a

@[inline] def mkForallAux (elimMVarDepsAux : Array Expr → Expr → M σ Expr) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : M σ Expr :=
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
def mkMVarApp (lctx : LocalContext) (mvar : Expr) (xs : Array Expr) : Expr :=
xs.foldl (fun e x => if (lctx.findFVar x).get!.isLet then e else Expr.app e x) mvar

partial def elimMVarDepsAux : Array Expr → Expr → M σ Expr
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
  match getExprAssignment mctx mvarId with
  | some a => visit (elimMVarDepsAux xs) a
  | none   =>
    let mvarDecl := getDecl mctx mvarId;
    let mvarLCtx := mvarDecl.lctx;
    let toRevert := getInScope mvarLCtx xs;
    if toRevert.size == 0 then
      pure e
    else if isReadOnlyExprMVar mctx mvarId then
      throw $ MkBindingException.readOnlyMVar mvarId
    else if !auxMVarSupport σ then
      throw MkBindingException.mkAuxMVarNotSupported
    else
      match collectDeps mctx mvarLCtx toRevert with
      | Except.error ex    => throw ex
      | Except.ok toRevert => do
        let newMVarLCtx   := reduceLocalContext mvarLCtx toRevert;
        newMVarType ← mkForallAux (fun xs e => elimMVarDepsAux xs e) mvarLCtx toRevert mvarDecl.type;
        mctx        ← getMCtx;
        newMVarId   ← mkFreshId;
        let mctx := mkAuxMVar mctx newMVarId newMVarLCtx newMVarType mvarDecl.synthetic;
        modify $ fun s => { mctx := mctx, .. s };
        let newMVar := Expr.mvar newMVarId;
        let result  := mkMVarApp mvarLCtx newMVar toRevert;
        if mvarDecl.synthetic then
          modify (fun s => { mctx := assignDelayed s.mctx newMVarId mvarLCtx toRevert e, .. s })
        else
          modify (fun s => { mctx := assignExpr s.mctx mvarId result, .. s });
        pure result
| xs, e => pure e

partial def elimMVarDeps (xs : Array Expr) (e : Expr) : M σ Expr :=
if !e.hasMVar then
  pure e
else
  withFreshCache $ elimMVarDepsAux xs e

end MkBinding

def mkBinding (isLambda : Bool) (mctx : σ) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr) : Except MkBindingException (σ × NameGenerator × Expr) :=
match (MkBinding.mkBinding isLambda MkBinding.elimMVarDeps lctx xs e).run { mctx := mctx, ngen := ngen } with
| EState.Result.ok e s      => Except.ok (s.mctx, s.ngen, e)
| EState.Result.error err _ => Except.error err

@[inline] def mkLambda (mctx : σ) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr) : Except MkBindingException (σ × NameGenerator × Expr) :=
mkBinding true mctx ngen lctx xs e

@[inline] def mkForall (mctx : σ) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr) : Except MkBindingException (σ × NameGenerator × Expr) :=
mkBinding false mctx ngen lctx xs e

end AbstractMetavarContext

export AbstractMetavarContext (MkBindingException)

end Lean
