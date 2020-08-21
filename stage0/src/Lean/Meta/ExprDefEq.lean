/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ProjFns
import Lean.Meta.WHNF
import Lean.Meta.InferType
import Lean.Meta.FunInfo
import Lean.Meta.LevelDefEq
import Lean.Meta.Check
import Lean.Meta.Offset

namespace Lean
namespace Meta

/--
  Try to solve `a := (fun x => t) =?= b` by eta-expanding `b`.

  Remark: eta-reduction is not a good alternative even in a system without universe cumulativity like Lean.
  Example:
    ```
    (fun x : A => f ?m) =?= f
    ```
    The left-hand side of the constraint above it not eta-reduced because `?m` is a metavariable. -/
private def isDefEqEta (a b : Expr) : MetaM Bool :=
if a.isLambda && !b.isLambda then do
  bType ← inferType b;
  bType ← whnfD bType;
  match bType with
  | Expr.forallE n d _ c =>
    let b' := Lean.mkLambda n c.binderInfo d (mkApp b (mkBVar 0));
    commitWhen $ isExprDefEqAux a b'
  | _ => pure false
else
  pure false

/-- Support for `Lean.reduceBool` and `Lean.reduceNat` -/
def isDefEqNative (s t : Expr) : MetaM LBool := do
let isDefEq (s t) : MetaM LBool := toLBoolM $ isExprDefEqAux s t;
s? ← reduceNative? s;
t? ← reduceNative? t;
match s?, t? with
| some s, some t => isDefEq s t
| some s, none   => isDefEq s t
| none,   some t => isDefEq s t
| none,   none   => pure LBool.undef

/-- Support for reducing Nat basic operations. -/
def isDefEqNat (s t : Expr) : MetaM LBool := do
let isDefEq (s t) : MetaM LBool := toLBoolM $ isExprDefEqAux s t;
if s.hasFVar || s.hasMVar || t.hasFVar || t.hasMVar then
  pure LBool.undef
else do
  s? ← reduceNat? s;
  t? ← reduceNat? t;
  match s?, t? with
  | some s, some t => isDefEq s t
  | some s, none   => isDefEq s t
  | none,   some t => isDefEq s t
  | none,   none   => pure LBool.undef

/-- Support for constraints of the form `("..." =?= String.mk cs)` -/
def isDefEqStringLit (s t : Expr) : MetaM LBool := do
let isDefEq (s t) : MetaM LBool := toLBoolM $ isExprDefEqAux s t;
if s.isStringLit && t.isAppOf `String.mk then
  isDefEq (WHNF.toCtorIfLit s) t
else if s.isAppOf `String.mk && t.isStringLit then
  isDefEq s (WHNF.toCtorIfLit t)
else
  pure LBool.undef

/--
  Return `true` if `e` is of the form `fun (x_1 ... x_n) => ?m x_1 ... x_n)`, and `?m` is unassigned.
  Remark: `n` may be 0. -/
def isEtaUnassignedMVar (e : Expr) : MetaM Bool :=
match e.etaExpanded? with
| some (Expr.mvar mvarId _) =>
  condM (isReadOnlyOrSyntheticOpaqueExprMVar mvarId)
    (pure false)
    (condM (isExprMVarAssigned mvarId)
      (pure false)
      (pure true))
| _   => pure false


/-
  First pass for `isDefEqArgs`. We unify explicit arguments, *and* easy cases
  Here, we say a case is easy if it is of the form

       ?m =?= t
       or
       t  =?= ?m

  where `?m` is unassigned.

  These easy cases are not just an optimization. When
  `?m` is a function, by assigning it to t, we make sure
  a unification constraint (in the explicit part)
  ```
  ?m t =?= f s
  ```
  is not higher-order.

  We also handle the eta-expanded cases:
  ```
  fun x₁ ... xₙ => ?m x₁ ... xₙ =?= t
  t =?= fun x₁ ... xₙ => ?m x₁ ... xₙ

  This is important because type inference often produces
  eta-expanded terms, and without this extra case, we could
  introduce counter intuitive behavior.

  Pre: `paramInfo.size <= args₁.size = args₂.size`
-/
private partial def isDefEqArgsFirstPass
    (paramInfo : Array ParamInfo) (args₁ args₂ : Array Expr) : Nat → Array Nat → MetaM (Option (Array Nat))
| i, postponed =>
  if h : i < paramInfo.size then
    let info := paramInfo.get ⟨i, h⟩;
    let a₁ := args₁.get! i;
    let a₂ := args₂.get! i;
    if info.implicit || info.instImplicit then
      condM (isEtaUnassignedMVar a₁ <||> isEtaUnassignedMVar a₂)
        (condM (isExprDefEqAux a₁ a₂)
          (isDefEqArgsFirstPass (i+1) postponed)
          (pure none))
        (isDefEqArgsFirstPass (i+1) (postponed.push i))
    else
      condM (isExprDefEqAux a₁ a₂)
        (isDefEqArgsFirstPass (i+1) postponed)
        (pure none)
  else
    pure (some postponed)

private partial def isDefEqArgsAux (args₁ args₂ : Array Expr) (h : args₁.size = args₂.size) : Nat → MetaM Bool
| i =>
  if h₁ : i < args₁.size then
    let a₁ := args₁.get ⟨i, h₁⟩;
    let a₂ := args₂.get ⟨i, h ▸ h₁⟩;
    condM (isExprDefEqAux a₁ a₂)
      (isDefEqArgsAux (i+1))
      (pure false)
  else
    pure true

@[specialize] private def trySynthPending (e : Expr) : MetaM Bool := do
mvarId? ← getStuckMVar? e;
match mvarId? with
| some mvarId => synthPending mvarId
| none        => pure false

private def isDefEqArgs (f : Expr) (args₁ args₂ : Array Expr) : MetaM Bool :=
if h : args₁.size = args₂.size then do
  finfo ← getFunInfoNArgs f args₁.size;
  (some postponed) ← isDefEqArgsFirstPass finfo.paramInfo args₁ args₂ 0 #[] | pure false;
  (isDefEqArgsAux args₁ args₂ h finfo.paramInfo.size)
  <&&>
  (postponed.allM $ fun i => do
   /- Second pass: unify implicit arguments.
      In the second pass, we make sure we are unfolding at
      least non reducible definitions (default setting). -/
    let a₁   := args₁.get! i;
    let a₂   := args₂.get! i;
    let info := finfo.paramInfo.get! i;
    when info.instImplicit $ do {
      _ ← trySynthPending a₁;
      _ ← trySynthPending a₂;
      pure ()
    };
    withAtLeastTransparency TransparencyMode.default $ isExprDefEqAux a₁ a₂)
else
  pure false

/--
  Check whether the types of the free variables at `fvars` are
  definitionally equal to the types at `ds₂`.

  Pre: `fvars.size == ds₂.size`

  This method also updates the set of local instances, and invokes
  the continuation `k` with the updated set.

  We can't use `withNewLocalInstances` because the `isDeq fvarType d₂`
  may use local instances. -/
@[specialize] partial def isDefEqBindingDomain (fvars : Array Expr) (ds₂ : Array Expr) : Nat → MetaM Bool → MetaM Bool
| i, k =>
  if h : i < fvars.size then do
    let fvar := fvars.get ⟨i, h⟩;
    fvarDecl ← getFVarLocalDecl fvar;
    let fvarType := fvarDecl.type;
    let d₂       := ds₂.get! i;
    condM (isExprDefEqAux fvarType d₂)
      (do c? ← isClass fvarType;
          match c? with
          | some className => withNewLocalInstance className fvar $ isDefEqBindingDomain (i+1) k
          | none           => isDefEqBindingDomain (i+1) k)
      (pure false)
  else
    k

/- Auxiliary function for `isDefEqBinding` for handling binders `forall/fun`.
   It accumulates the new free variables in `fvars`, and declare them at `lctx`.
   We use the domain types of `e₁` to create the new free variables.
   We store the domain types of `e₂` at `ds₂`. -/
private partial def isDefEqBindingAux : LocalContext → Array Expr → Expr → Expr → Array Expr → MetaM Bool
| lctx, fvars, e₁, e₂, ds₂ =>
  let process (n : Name) (d₁ d₂ b₁ b₂ : Expr) : MetaM Bool := do {
    let d₁    := d₁.instantiateRev fvars;
    let d₂    := d₂.instantiateRev fvars;
    fvarId    ← mkFreshId;
    let lctx  := lctx.mkLocalDecl fvarId n d₁;
    let fvars := fvars.push (mkFVar fvarId);
    isDefEqBindingAux lctx fvars b₁ b₂ (ds₂.push d₂)
  };
  match e₁, e₂ with
  | Expr.forallE n d₁ b₁ _, Expr.forallE _ d₂ b₂ _ => process n d₁ d₂ b₁ b₂
  | Expr.lam     n d₁ b₁ _, Expr.lam     _ d₂ b₂ _ => process n d₁ d₂ b₁ b₂
  | _,                      _                      =>
    adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
      isDefEqBindingDomain fvars ds₂ 0 $
        isExprDefEqAux (e₁.instantiateRev fvars) (e₂.instantiateRev fvars)

@[inline] private def isDefEqBinding (a b : Expr) : MetaM Bool := do
lctx ← getLCtx;
isDefEqBindingAux lctx #[] a b #[]

private def checkTypesAndAssign (mvar : Expr) (v : Expr) : MetaM Bool :=
traceCtx `Meta.isDefEq.assign.checkTypes $ do
  -- must check whether types are definitionally equal or not, before assigning and returning true
  mvarType ← inferType mvar;
  vType    ← inferType v;
  condM (withTransparency TransparencyMode.default $ isExprDefEqAux mvarType vType)
    (do trace! `Meta.isDefEq.assign.final (mvar ++ " := " ++ v);
        assignExprMVar mvar.mvarId! v; pure true)
    (do trace `Meta.isDefEq.assign.typeMismatch $ fun _ => mvar ++ " : " ++ mvarType ++ " := " ++ v ++ " : " ++ vType;
        pure false)

/-
  Each metavariable is declared in a particular local context.
  We use the notation `C |- ?m : t` to denote a metavariable `?m` that
  was declared at the local context `C` with type `t` (see `MetavarDecl`).
  We also use `?m@C` as a shorthand for `C |- ?m : t` where `t` is the type of `?m`.

  The following method process the unification constraint

       ?m@C a₁ ... aₙ =?= t

  We say the unification constraint is a pattern IFF

    1) `a₁ ... aₙ` are pairwise distinct free variables that are ​*not*​ let-variables.
    2) `a₁ ... aₙ` are not in `C`
    3) `t` only contains free variables in `C` and/or `{a₁, ..., aₙ}`
    4) For every metavariable `?m'@C'` occurring in `t`, `C'` is a subprefix of `C`
    5) `?m` does not occur in `t`

  Claim: we don't have to check free variable declarations. That is,
  if `t` contains a reference to `x : A := v`, we don't need to check `v`.
  Reason: The reference to `x` is a free variable, and it must be in `C` (by 1 and 3).
  If `x` is in `C`, then any metavariable occurring in `v` must have been defined in a strict subprefix of `C`.
  So, condition 4 and 5 are satisfied.

  If the conditions above have been satisfied, then the
  solution for the unification constrain is

    ?m := fun a₁ ... aₙ => t

  Now, we consider some workarounds/approximations.

 A1) Suppose `t` contains a reference to `x : A := v` and `x` is not in `C` (failed condition 3)
     (precise) solution: unfold `x` in `t`.

 A2) Suppose some `aᵢ` is in `C` (failed condition 2)
     (approximated) solution (when `config.foApprox` is set to true) :
     ignore condition and also use

        ?m := fun a₁ ... aₙ => t

   Here is an example where this approximation fails:
   Given `C` containing `a : nat`, consider the following two constraints
         ?m@C a =?= a
         ?m@C b =?= a

   If we use the approximation in the first constraint, we get
         ?m := fun x => x
   when we apply this solution to the second one we get a failure.

   IMPORTANT: When applying this approximation we need to make sure the
   abstracted term `fun a₁ ... aₙ => t` is type correct. The check
   can only be skipped in the pattern case described above. Consider
   the following example. Given the local context

      (α : Type) (a : α)

   we try to solve

     ?m α =?= @id α a

   If we use the approximation above we obtain:

     ?m := (fun α' => @id α' a)

   which is a type incorrect term. `a` has type `α` but it is expected to have
   type `α'`.

   The problem occurs because the right hand side contains a free variable
   `a` that depends on the free variable `α` being abstracted. Note that
   this dependency cannot occur in patterns.

   We can address this by type checking
   the term after abstraction. This is not a significant performance
   bottleneck because this case doesn't happen very often in practice
   (262 times when compiling stdlib on Jan 2018). The second example
   is trickier, but it also occurs less frequently (8 times when compiling
   stdlib on Jan 2018, and all occurrences were at Init/Control when
   we define monads and auxiliary combinators for them).
   We considered three options for the addressing the issue on the second example:

 A3) `a₁ ... aₙ` are not pairwise distinct (failed condition 1).
   In Lean3, we would try to approximate this case using an approach similar to A2.
   However, this approximation complicates the code, and is never used in the
   Lean3 stdlib and mathlib.

 A4) `t` contains a metavariable `?m'@C'` where `C'` is not a subprefix of `C`.
   If `?m'` is assigned, we substitute.
   If not, we create an auxiliary metavariable with a smaller scope.
   Actually, we let `elimMVarDeps` at `MetavarContext.lean` to perform this step.

 A5) If some `aᵢ` is not a free variable,
     then we use first-order unification (if `config.foApprox` is set to true)

       ?m a_1 ... a_i a_{i+1} ... a_{i+k} =?= f b_1 ... b_k

   reduces to

       ?M a_1 ... a_i =?= f
       a_{i+1}        =?= b_1
       ...
       a_{i+k}        =?= b_k


 A6) If (m =?= v) is of the form

        ?m a_1 ... a_n =?= ?m b_1 ... b_k

     then we use first-order unification (if `config.foApprox` is set to true)
-/

namespace CheckAssignment

structure State :=
(cache : ExprStructMap Expr := {})

structure Context :=
(mvarId        : MVarId)
(mvarDecl      : MetavarDecl)
(fvars         : Array Expr)
(hasCtxLocals  : Bool)

inductive Exception
| occursCheck
| useFOApprox
| outOfScopeFVar             (fvarId : FVarId)
| readOnlyMVarWithBiggerLCtx (mvarId : MVarId)
| unknownExprMVar            (mvarId : MVarId)
| meta                       (ex : Meta.Exception)

instance : MonadIO (EIO Exception) :=
mkEIOMonadIO Exception.meta

abbrev CheckAssignmentM := ReaderT Context $ StateRefT State $ EMetaM Exception

@[inline] def liftMetaM {α} (x : MetaM α) : CheckAssignmentM α :=
liftM (adaptExcept Exception.meta x : EMetaM Exception α)

private def findCached? (e : Expr) : CheckAssignmentM (Option Expr) := do
s ← get;
pure $ s.cache.find? e

private def cache (e r : Expr) : CheckAssignmentM Unit := do
modify fun s => { s with cache := s.cache.insert e r }

instance : MonadCache Expr Expr CheckAssignmentM :=
{ findCached? := findCached?, cache := cache }

@[inline] private def visit (f : Expr → CheckAssignmentM Expr) (e : Expr) : CheckAssignmentM Expr :=
if !e.hasExprMVar && !e.hasFVar then pure e else checkCache e f

@[inline] private def readMeta : CheckAssignmentM Meta.Context := do
liftMetaM read

@[specialize] def checkFVar (check : Expr → CheckAssignmentM Expr) (fvar : Expr) : CheckAssignmentM Expr := do
ctxMeta ← readMeta;
ctx ← read;
if ctx.mvarDecl.lctx.containsFVar fvar then pure fvar
else do
  let lctx := ctxMeta.lctx;
  match lctx.findFVar? fvar with
  | some (LocalDecl.ldecl _ _ _ _ v) => visit check v
  | _ =>
    if ctx.fvars.contains fvar then pure fvar
    else throw $ Exception.outOfScopeFVar fvar.fvarId!

@[inline] def getMCtx : CheckAssignmentM MetavarContext := do
liftMetaM Meta.getMCtx

def mkAuxMVar (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr) : CheckAssignmentM Expr := do
liftMetaM $ mkFreshExprMVarAt lctx localInsts type

@[specialize] def checkMVar (check : Expr → CheckAssignmentM Expr) (mvar : Expr) : CheckAssignmentM Expr := do
let mvarId := mvar.mvarId!;
ctx  ← read;
mctx ← getMCtx;
if mvarId == ctx.mvarId then throw Exception.occursCheck
else match mctx.getExprAssignment? mvarId with
  | some v => check v
  | none   => match mctx.findDecl? mvarId with
    | none          => throw $ Exception.unknownExprMVar mvarId
    | some mvarDecl =>
      if ctx.hasCtxLocals then
        throw $ Exception.useFOApprox -- It is not a pattern, then we fail and fall back to FO unification
      else if mvarDecl.lctx.isSubPrefixOf ctx.mvarDecl.lctx ctx.fvars then
        /- The local context of `mvar` - free variables being abstracted is a subprefix of the metavariable being assigned.
           We "substract" variables being abstracted because we use `elimMVarDeps` -/
        pure mvar
      else if mvarDecl.depth != mctx.depth || mvarDecl.kind.isSyntheticOpaque then throw $ Exception.readOnlyMVarWithBiggerLCtx mvarId
      else do
        ctxMeta ← readMeta;
        if ctxMeta.config.ctxApprox && ctx.mvarDecl.lctx.isSubPrefixOf mvarDecl.lctx then do
          mvarType ← check mvarDecl.type;
          /- Create an auxiliary metavariable with a smaller context and "checked" type.
             Note that `mvarType` may be different from `mvarDecl.type`. Example: `mvarType` contains
             a metavariable that we also need to reduce the context. -/
          newMVar ← mkAuxMVar ctx.mvarDecl.lctx ctx.mvarDecl.localInstances mvarType;
          liftMetaM $ modify (fun s => { s with mctx := s.mctx.assignExpr mvarId newMVar });
          pure newMVar
        else
          pure mvar

/-
  Auxiliary function used to "fix" subterms of the form `?m x_1 ... x_n` where `x_i`s are free variables,
  and one of them is out-of-scope.
  See `Expr.app` case at `check`.
  If `ctxApprox` is true, then we solve this case by creating a fresh metavariable ?n with the correct scope,
  an assigning `?m := fun _ ... _ => ?n` -/
def assignToConstFun (mvar : Expr) (numArgs : Nat) (newMVar : Expr) : MetaM Bool := do
mvarType ← inferType mvar;
forallBoundedTelescope mvarType numArgs $ fun xs _ =>
  if xs.size != numArgs then pure false
  else do
    v ← mkLambda xs newMVar;
    checkTypesAndAssign mvar v

partial def check : Expr → CheckAssignmentM Expr
| e@(Expr.mdata _ b _)     => do b ← visit check b; pure $ e.updateMData! b
| e@(Expr.proj _ _ s _)    => do s ← visit check s; pure $ e.updateProj! s
| e@(Expr.lam _ d b _)     => do d ← visit check d; b ← visit check b; pure $ e.updateLambdaE! d b
| e@(Expr.forallE _ d b _) => do d ← visit check d; b ← visit check b; pure $ e.updateForallE! d b
| e@(Expr.letE _ t v b _)  => do t ← visit check t; v ← visit check v; b ← visit check b; pure $ e.updateLet! t v b
| e@(Expr.bvar _ _)        => pure e
| e@(Expr.sort _ _)        => pure e
| e@(Expr.const _ _ _)     => pure e
| e@(Expr.lit _ _)         => pure e
| e@(Expr.fvar _ _)        => visit (checkFVar check) e
| e@(Expr.mvar _ _)        => visit (checkMVar check) e
| Expr.localE _ _ _ _      => unreachable!
| e@(Expr.app _ _ _)       => e.withApp $ fun f args => do
  ctxMeta ← readMeta;
  if f.isMVar && ctxMeta.config.ctxApprox && args.all Expr.isFVar then do
    f ← visit (checkMVar check) f;
    catch
      (do
        args ← args.mapM (visit check);
        pure $ mkAppN f args)
      (fun ex => match ex with
        | Exception.outOfScopeFVar _ =>
          condM (liftMetaM $ isDelayedAssigned f.mvarId!) (throw ex) $ do
            eType ← liftMetaM $ inferType e;
            mvarType ← check eType;
            /- Create an auxiliary metavariable with a smaller context and "checked" type, assign `?f := fun _ => ?newMVar`
               Note that `mvarType` may be different from `eType`. -/
            ctx ← read;
            newMVar ← mkAuxMVar ctx.mvarDecl.lctx ctx.mvarDecl.localInstances mvarType;
            condM (liftMetaM $ assignToConstFun f args.size newMVar)
              (pure newMVar)
              (throw ex)
        | _ => throw ex)
  else do
    f ← visit check f;
    args ← args.mapM (visit check);
    pure $ mkAppN f args

@[inline] def run (x : CheckAssignmentM Expr) (mvarId : MVarId) (fvars : Array Expr) (hasCtxLocals : Bool) (v : Expr) : MetaM (Option Expr) := do
mvarDecl ← getMVarDecl mvarId;
let ctx := { mvarId := mvarId, mvarDecl := mvarDecl, fvars := fvars, hasCtxLocals := hasCtxLocals : Context };
let x : CheckAssignmentM (Option Expr) :=
  catch
    (do e ← x; pure $ some e)
    (fun ex =>
      match ex with
      | Exception.occursCheck => do
        trace! `Meta.isDefEq.assign.occursCheck (mkMVar mvarId ++ " " ++ fvars ++ " := " ++ v);
        pure none
      | Exception.useFOApprox =>
        pure none
      | Exception.outOfScopeFVar fvarId => do
        trace! `Meta.isDefEq.assign.outOfScopeFVar (mkFVar fvarId ++ " @ " ++ mkMVar mvarId ++ " " ++ fvars ++ " := " ++ v);
        pure none
      | Exception.readOnlyMVarWithBiggerLCtx nestedMVarId => do
        trace! `Meta.isDefEq.assign.readOnlyMVarWithBiggerLCtx (mkMVar nestedMVarId ++ " @ " ++ mkMVar mvarId ++ " " ++ fvars ++ " := " ++ v);
        pure none
      | Exception.unknownExprMVar mvarId =>
        -- This case can only happen if the MetaM API is being misused
        liftMetaM (throwUnknownMVar mvarId)
      | Exception.meta _ => throw ex);
let x : EMetaM Exception (Option Expr) := (x.run ctx).run' {};
adaptExcept
  (fun ex => match ex with
    | Exception.meta ex => ex
    | _                 => unreachable!)
  x

end CheckAssignment

namespace CheckAssignmentQuick

@[inline] private def visit (f : Expr → Bool) (e : Expr) : Bool :=
if !e.hasExprMVar && !e.hasFVar then true else f e

partial def check
    (hasCtxLocals ctxApprox : Bool)
    (mctx : MetavarContext) (lctx : LocalContext) (mvarDecl : MetavarDecl) (mvarId : MVarId) (fvars : Array Expr) : Expr → Bool
| e@(Expr.mdata _ b _)     => check b
| e@(Expr.proj _ _ s _)    => check s
| e@(Expr.app f a _)       => visit check f && visit check a
| e@(Expr.lam _ d b _)     => visit check d && visit check b
| e@(Expr.forallE _ d b _) => visit check d && visit check b
| e@(Expr.letE _ t v b _)  => visit check t && visit check v && visit check b
| e@(Expr.bvar _ _)        => true
| e@(Expr.sort _ _)        => true
| e@(Expr.const _ _ _)     => true
| e@(Expr.lit _ _)         => true
| e@(Expr.fvar fvarId _)   =>
  if mvarDecl.lctx.contains fvarId then true
  else match lctx.find? fvarId with
    | some (LocalDecl.ldecl _ _ _ _ v) => false -- need expensive CheckAssignment.check
    | _ =>
      if fvars.any $ fun x => x.fvarId! == fvarId then true
      else false -- We could throw an exception here, but we would have to use ExceptM. So, we let CheckAssignment.check do it
| e@(Expr.mvar mvarId' _)        => do
  match mctx.getExprAssignment? mvarId' with
  | some _ => false -- use CheckAssignment.check to instantiate
  | none   =>
    if mvarId' == mvarId then false -- occurs check failed, use CheckAssignment.check to throw exception
    else match mctx.findDecl? mvarId' with
      | none           => false
      | some mvarDecl' =>
        if hasCtxLocals then false -- use CheckAssignment.check
        else if mvarDecl'.lctx.isSubPrefixOf mvarDecl.lctx fvars then true
        else if mvarDecl'.depth != mctx.depth || mvarDecl'.kind.isSyntheticOpaque then false  -- use CheckAssignment.check
        else if ctxApprox && mvarDecl.lctx.isSubPrefixOf mvarDecl'.lctx then false  -- use CheckAssignment.check
        else true
| Expr.localE _ _ _ _      => unreachable!

end CheckAssignmentQuick

-- See checkAssignment
def checkAssignmentAux (mvarId : MVarId) (fvars : Array Expr) (hasCtxLocals : Bool) (v : Expr) : MetaM (Option Expr) := do
CheckAssignment.run (CheckAssignment.check v) mvarId fvars hasCtxLocals v

/--
  Auxiliary function for handling constraints of the form `?m a₁ ... aₙ =?= v`.
  It will check whether we can perform the assignment
  ```
  ?m := fun fvars => t
  ```
  The result is `none` if the assignment can't be performed.
  The result is `some newV` where `newV` is a possibly updated `v`. This method may need
  to unfold let-declarations. -/
def checkAssignment (mvarId : MVarId) (fvars : Array Expr) (v : Expr) : MetaM (Option Expr) := do
if !v.hasExprMVar && !v.hasFVar then
  pure (some v)
else do
  mvarDecl ← getMVarDecl mvarId;
  let hasCtxLocals := fvars.any $ fun fvar => mvarDecl.lctx.containsFVar fvar;
  ctx ← read;
  mctx ← getMCtx;
  if CheckAssignmentQuick.check hasCtxLocals ctx.config.ctxApprox mctx ctx.lctx mvarDecl mvarId fvars v then
    pure (some v)
  else do
    v ← instantiateMVars v;
    checkAssignmentAux mvarId fvars hasCtxLocals v

private def processAssignmentFOApproxAux (mvar : Expr) (args : Array Expr) (v : Expr) : MetaM Bool :=
match v with
| Expr.app f a _ => isExprDefEqAux args.back a <&&> isExprDefEqAux (mkAppRange mvar 0 (args.size - 1) args) f
| _              => pure false

/-
  Auxiliary method for applying first-order unification. It is an approximation.
  Remark: this method is trying to solve the unification constraint:

      ?m a₁ ... aₙ =?= v

   It is uses processAssignmentFOApproxAux, if it fails, it tries to unfold `v`.

   We have added support for unfolding here because we want to be able to solve unification problems such as

      ?m Unit =?= ITactic

   where `ITactic` is defined as

   def ITactic := Tactic Unit
-/
private partial def processAssignmentFOApprox (mvar : Expr) (args : Array Expr) : Expr → MetaM Bool
| v => do
  cfg ← getConfig;
  if !cfg.foApprox then pure false
  else do
    trace! `Meta.isDefEq.foApprox (mvar ++ " " ++ args ++ " := " ++ v);
    condM (commitWhen $ processAssignmentFOApproxAux mvar args v)
      (pure true)
      (do v? ← unfoldDefinition? v;
          match v? with
          | none   => pure false
          | some v => processAssignmentFOApprox v)

private partial def simpAssignmentArgAux : Expr → MetaM Expr
| Expr.mdata _ e _       => simpAssignmentArgAux e
| e@(Expr.fvar fvarId _) => do
  decl ← getLocalDecl fvarId;
  match decl.value? with
  | some value => simpAssignmentArgAux value
  | _          => pure e
| e => pure e

/- Auxiliary procedure for processing `?m a₁ ... aₙ =?= v`.
   We apply it to each `aᵢ`. It instantiates assigned metavariables if `aᵢ` is of the form `f[?n] b₁ ... bₘ`,
   and then removes metadata, and zeta-expand let-decls. -/
private def simpAssignmentArg (arg : Expr) : MetaM Expr := do
arg ← if arg.getAppFn.hasExprMVar then instantiateMVars arg else pure arg;
simpAssignmentArgAux arg

private def processConstApprox (mvar : Expr) (numArgs : Nat) (v : Expr) : MetaM Bool := do
cfg ← getConfig;
if cfg.constApprox then do
  let mvarId := mvar.mvarId!;
  v? ← checkAssignment mvarId #[] v;
  match v? with
  | none   => pure false
  | some v => do
    mvarDecl ← getMVarDecl mvarId;
    forallBoundedTelescope mvarDecl.type numArgs $ fun xs _ =>
      if xs.size != numArgs then pure false
      else do
        v ← mkLambda xs v;
        checkTypesAndAssign mvar v
else
  pure false

private partial def processAssignmentAux (mvar : Expr) (mvarDecl : MetavarDecl) : Nat → Array Expr → Expr → MetaM Bool
| i, args, v => do
  cfg ← getConfig;
  let useFOApprox (args : Array Expr) : MetaM Bool :=
    processAssignmentFOApprox mvar args v <||> processConstApprox mvar args.size v;
  if h : i < args.size then do
    let arg := args.get ⟨i, h⟩;
    arg ← simpAssignmentArg arg;
    let args := args.set ⟨i, h⟩ arg;
    match arg with
    | Expr.fvar fvarId _ =>
      if args.anyRange 0 i (fun prevArg => prevArg == arg) then
        useFOApprox args
      else if mvarDecl.lctx.contains fvarId && !cfg.quasiPatternApprox then
        useFOApprox args
      else
        processAssignmentAux (i+1) args v
    | _ =>
      useFOApprox args
  else do
    v ← instantiateMVars v; -- enforce A4
    if v.getAppFn == mvar then
      -- using A6
      useFOApprox args
    else do
      let mvarId := mvar.mvarId!;
      v? ← checkAssignment mvarId args v;
      match v? with
      | none   => useFOApprox args
      | some v => do
        trace `Meta.isDefEq.assign.beforeMkLambda $ fun _ => mvar ++ " " ++ args ++ " := " ++ v;
        v ← mkLambda args v;
        if args.any (fun arg => mvarDecl.lctx.containsFVar arg) then
          /- We need to type check `v` because abstraction using `mkLambda` may have produced
             a type incorrect term. See discussion at A2 -/
          condM (isTypeCorrect v)
            (checkTypesAndAssign mvar v)
            (do trace `Meta.isDefEq.assign.typeError $ fun _ => mvar ++ " := " ++ v;
                useFOApprox args)
        else
          checkTypesAndAssign mvar v

/-- Tries to solve `?m a₁ ... aₙ =?= v` by assigning `?m`.
    It assumes `?m` is unassigned. -/
private def processAssignment (mvarApp : Expr) (v : Expr) : MetaM Bool :=
traceCtx `Meta.isDefEq.assign $ do
  trace! `Meta.isDefEq.assign (mvarApp ++ " := " ++ v);
  let mvar := mvarApp.getAppFn;
  mvarDecl ← getMVarDecl mvar.mvarId!;
  processAssignmentAux mvar mvarDecl 0 mvarApp.getAppArgs v

private def isDeltaCandidate (t : Expr) : MetaM (Option ConstantInfo) :=
match t.getAppFn with
| Expr.const c _ _ => getConst c
| _                => pure none

/-- Auxiliary method for isDefEqDelta -/
private def isListLevelDefEq (us vs : List Level) : MetaM LBool :=
toLBoolM $ isListLevelDefEqAux us vs

/-- Auxiliary method for isDefEqDelta -/
private def isDefEqLeft (fn : Name) (t s : Expr) : MetaM LBool := do
trace! `Meta.isDefEq.delta.unfoldLeft fn;
toLBoolM $ isExprDefEqAux t s

/-- Auxiliary method for isDefEqDelta -/
private def isDefEqRight (fn : Name) (t s : Expr) : MetaM LBool := do
trace! `Meta.isDefEq.delta.unfoldRight fn;
toLBoolM $ isExprDefEqAux t s

/-- Auxiliary method for isDefEqDelta -/
private def isDefEqLeftRight (fn : Name) (t s : Expr) : MetaM LBool := do
trace! `Meta.isDefEq.delta.unfoldLeftRight fn;
toLBoolM $ isExprDefEqAux t s

/-- Try to solve `f a₁ ... aₙ =?= f b₁ ... bₙ` by solving `a₁ =?= b₁, ..., aₙ =?= bₙ`.

    Auxiliary method for isDefEqDelta -/
private def tryHeuristic (t s : Expr) : MetaM Bool :=
let tFn := t.getAppFn;
let sFn := s.getAppFn;
traceCtx `Meta.isDefEq.delta $
  commitWhen $ do
    b ← isDefEqArgs tFn t.getAppArgs s.getAppArgs
        <&&>
        isListLevelDefEqAux tFn.constLevels! sFn.constLevels!;
    unless b $ trace! `Meta.isDefEq.delta ("heuristic failed " ++ t ++ " =?= " ++ s);
    pure b

/-- Auxiliary method for isDefEqDelta -/
private abbrev unfold {α} (e : Expr) (failK : MetaM α) (successK : Expr → MetaM α) : MetaM α := do
e? ← unfoldDefinition? e;
match e? with
| some e => successK e
| none   => failK

/-- Auxiliary method for isDefEqDelta -/
private def unfoldBothDefEq (fn : Name) (t s : Expr) : MetaM LBool :=
match t, s with
| Expr.const _ ls₁ _, Expr.const _ ls₂ _ => isListLevelDefEq ls₁ ls₂
| Expr.app _ _ _,     Expr.app _ _ _     =>
  condM (tryHeuristic t s)
    (pure LBool.true)
    (unfold t
      (unfold s (pure LBool.false) (fun s => isDefEqRight fn t s))
      (fun t => unfold s (isDefEqLeft fn t s) (fun s => isDefEqLeftRight fn t s)))
| _, _ => pure LBool.false

private def sameHeadSymbol (t s : Expr) : Bool :=
match t.getAppFn, s.getAppFn with
| Expr.const c₁ _ _, Expr.const c₂ _ _ => true
| _,                 _                 => false

/--
  - If headSymbol (unfold t) == headSymbol s, then unfold t
  - If headSymbol (unfold s) == headSymbol t, then unfold s
  - Otherwise unfold t and s if possible.

  Auxiliary method for isDefEqDelta -/
private def unfoldComparingHeadsDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool :=
unfold t
  (unfold s
    (pure LBool.undef) -- `t` and `s` failed to be unfolded
    (fun s => isDefEqRight sInfo.name t s))
  (fun tNew =>
    if sameHeadSymbol tNew s then
      isDefEqLeft tInfo.name tNew s
    else
      unfold s
        (isDefEqLeft tInfo.name tNew s)
        (fun sNew =>
          if sameHeadSymbol t sNew then
            isDefEqRight sInfo.name t sNew
          else
            isDefEqLeftRight tInfo.name tNew sNew))

/-- If `t` and `s` do not contain metavariables, then use
    kernel definitional equality heuristics.
    Otherwise, use `unfoldComparingHeadsDefEq`.

    Auxiliary method for isDefEqDelta -/
private def unfoldDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool :=
if !t.hasExprMVar && !s.hasExprMVar then
  /- If `t` and `s` do not contain metavariables,
     we simulate strategy used in the kernel. -/
  if tInfo.hints.lt sInfo.hints then
    unfold t (unfoldComparingHeadsDefEq tInfo sInfo t s) $ fun t => isDefEqLeft tInfo.name t s
  else if sInfo.hints.lt tInfo.hints then
    unfold s (unfoldComparingHeadsDefEq tInfo sInfo t s) $ fun s => isDefEqRight sInfo.name t s
  else
    unfoldComparingHeadsDefEq tInfo sInfo t s
else
  unfoldComparingHeadsDefEq tInfo sInfo t s

/--
  When `TransparencyMode` is set to `default` or `all`.
  If `t` is reducible and `s` is not ==> `isDefEqLeft  (unfold t) s`
  If `s` is reducible and `t` is not ==> `isDefEqRight t (unfold s)`

  Otherwise, use `unfoldDefEq`

  Auxiliary method for isDefEqDelta -/
private def unfoldReducibeDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool :=
condM shouldReduceReducibleOnly
  (unfoldDefEq tInfo sInfo t s)
  (do tReducible ← isReducible tInfo.name;
      sReducible ← isReducible sInfo.name;
      if tReducible && !sReducible then
        unfold t (unfoldDefEq tInfo sInfo t s) $ fun t => isDefEqLeft tInfo.name t s
      else if !tReducible && sReducible then
        unfold s (unfoldDefEq tInfo sInfo t s) $ fun s => isDefEqRight sInfo.name t s
      else
        unfoldDefEq tInfo sInfo t s)

/--
  If `t` is a projection function application and `s` is not ==> `isDefEqRight t (unfold s)`
  If `s` is a projection function application and `t` is not ==> `isDefEqRight (unfold t) s`

  Otherwise, use `unfoldReducibeDefEq`

  Auxiliary method for isDefEqDelta -/
private def unfoldNonProjFnDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool := do
env ← getEnv;
let tProj? := env.isProjectionFn tInfo.name;
let sProj? := env.isProjectionFn sInfo.name;
if tProj? && !sProj? then
  unfold s (unfoldDefEq tInfo sInfo t s) $ fun s => isDefEqRight sInfo.name t s
else if !tProj? && sProj? then
  unfold t (unfoldDefEq tInfo sInfo t s) $ fun t => isDefEqLeft tInfo.name t s
else
  unfoldReducibeDefEq tInfo sInfo t s

/--
  isDefEq by lazy delta reduction.
  This method implements many different heuristics:
  1- If only `t` can be unfolded => then unfold `t` and continue
  2- If only `s` can be unfolded => then unfold `s` and continue
  3- If `t` and `s` can be unfolded and they have the same head symbol, then
     a) First try to solve unification by unifying arguments.
     b) If it fails, unfold both and continue.
     Implemented by `unfoldBothDefEq`
  4- If `t` is a projection function application and `s` is not => then unfold `s` and continue.
  5- If `s` is a projection function application and `t` is not => then unfold `t` and continue.
  Remark: 4&5 are implemented by `unfoldNonProjFnDefEq`
  6- If `t` is reducible and `s` is not => then unfold `t` and continue.
  7- If `s` is reducible and `t` is not => then unfold `s` and continue
  Remark: 6&7 are implemented by `unfoldReducibeDefEq`
  8- If `t` and `s` do not contain metavariables, then use heuristic used in the Kernel.
     Implemented by `unfoldDefEq`
  9- If `headSymbol (unfold t) == headSymbol s`, then unfold t and continue.
  10- If `headSymbol (unfold s) == headSymbol t`, then unfold s
  11- Otherwise, unfold `t` and `s` and continue.
  Remark: 9&10&11 are implemented by `unfoldComparingHeadsDefEq` -/
private def isDefEqDelta (t s : Expr) : MetaM LBool := do
tInfo? ← isDeltaCandidate t.getAppFn;
sInfo? ← isDeltaCandidate s.getAppFn;
match tInfo?, sInfo? with
| none,       none       => pure LBool.undef
| some tInfo, none       => unfold t (pure LBool.undef) $ fun t => isDefEqLeft tInfo.name t s
| none,       some sInfo => unfold s (pure LBool.undef) $ fun s => isDefEqRight sInfo.name t s
| some tInfo, some sInfo =>
  if tInfo.name == sInfo.name then
    unfoldBothDefEq tInfo.name t s
  else
    unfoldNonProjFnDefEq tInfo sInfo t s

private def isAssigned : Expr → MetaM Bool
| Expr.mvar mvarId _ => isExprMVarAssigned mvarId
| _                  => pure false

private def isDelayedAssignedHead (tFn : Expr) (t : Expr) : MetaM Bool :=
match tFn with
| Expr.mvar mvarId _ => do
  condM (isDelayedAssigned mvarId)
    (do tNew ← instantiateMVars t;
        pure $ tNew != t)
    (pure false)
| _ => pure false

private def isSynthetic : Expr → MetaM Bool
| Expr.mvar mvarId _ => do
  mvarDecl ← getMVarDecl mvarId;
  match mvarDecl.kind with
  | MetavarKind.synthetic       => pure true
  | MetavarKind.syntheticOpaque => pure true
  | MetavarKind.natural         => pure false
| _                  => pure false

private def isAssignable : Expr → MetaM Bool
| Expr.mvar mvarId _ => do b ← isReadOnlyOrSyntheticOpaqueExprMVar mvarId; pure (!b)
| _                  => pure false

private def etaEq (t s : Expr) : Bool :=
match t.etaExpanded? with
| some t => t == s
| none   => false

private def isLetFVar (fvarId : FVarId) : MetaM Bool := do
decl ← getLocalDecl fvarId;
pure decl.isLet

private def isDefEqProofIrrel (t s : Expr) : MetaM LBool := do
status ← isProofQuick t;
match status with
| LBool.false =>
  pure LBool.undef
| LBool.true  => do
  tType ← inferType t;
  sType ← inferType s;
  toLBoolM $ isExprDefEqAux tType sType
| LBool.undef => do
  tType ← inferType t;
  condM (isProp tType)
    (do sType ← inferType s; toLBoolM $ isExprDefEqAux tType sType)
    (pure LBool.undef)

private partial def isDefEqQuick : Expr → Expr → MetaM LBool
| Expr.lit  l₁ _,           Expr.lit l₂ _            => pure (l₁ == l₂).toLBool
| Expr.sort u _,            Expr.sort v _            => toLBoolM $ isLevelDefEqAux u v
| t@(Expr.lam _ _ _ _),     s@(Expr.lam _ _ _ _)     => if t == s then pure LBool.true else toLBoolM $ isDefEqBinding t s
| t@(Expr.forallE _ _ _ _), s@(Expr.forallE _ _ _ _) => if t == s then pure LBool.true else toLBoolM $ isDefEqBinding t s
| Expr.mdata _ t _,         s                        => isDefEqQuick t s
| t,                        Expr.mdata _ s _         => isDefEqQuick t s
| t@(Expr.fvar fvarId₁ _),  s@(Expr.fvar fvarId₂ _)  =>
  condM (isLetFVar fvarId₁ <||> isLetFVar fvarId₂)
    (pure LBool.undef)
    (if fvarId₁ == fvarId₂ then pure LBool.true else isDefEqProofIrrel t s)
| t, s =>
  cond (t == s) (pure LBool.true) $
  cond (etaEq t s || etaEq s t) (pure LBool.true) $  -- t =?= (fun xs => t xs)
  let tFn := t.getAppFn;
  let sFn := s.getAppFn;
  cond (!tFn.isMVar && !sFn.isMVar) (pure LBool.undef) $
  condM (isAssigned tFn) (do t ← instantiateMVars t; isDefEqQuick t s) $
  condM (isAssigned sFn) (do s ← instantiateMVars s; isDefEqQuick t s) $
  condM (isDelayedAssignedHead tFn t) (do t ← instantiateMVars t; isDefEqQuick t s) $
  condM (isDelayedAssignedHead sFn s) (do s ← instantiateMVars s; isDefEqQuick t s) $
  condM (isSynthetic tFn <&&> trySynthPending tFn) (do t ← instantiateMVars t; isDefEqQuick t s) $
  condM (isSynthetic sFn <&&> trySynthPending sFn) (do s ← instantiateMVars s; isDefEqQuick t s) $ do
  tAssign? ← isAssignable tFn;
  sAssign? ← isAssignable sFn;
  trace! `Meta.isDefEq
    (t ++ (if tAssign? then " [assignable]" else " [nonassignable]") ++ " =?= " ++ s ++ (if sAssign? then " [assignable]" else " [nonassignable]"));
  let assign (t s : Expr) : MetaM LBool := toLBoolM $ processAssignment t s;
  cond (tAssign? && !sAssign?)  (assign t s) $
  cond (!tAssign? && sAssign?)  (assign s t) $
  cond (!tAssign? && !sAssign?)
    (if tFn.isMVar || sFn.isMVar then do
       ctx ← read;
       if ctx.config.isDefEqStuckEx then do
         trace! `Meta.isDefEq.stuck (t ++ " =?= " ++ s);
         throwEx $ Exception.isExprDefEqStuck t s
       else pure LBool.false
     else pure LBool.undef) $ do
  -- Both `t` and `s` are terms of the form `?m ...`
  tMVarDecl ← getMVarDecl tFn.mvarId!;
  sMVarDecl ← getMVarDecl sFn.mvarId!;
  if s.isMVar && !t.isMVar then
    /- Solve `?m t =?= ?n` by trying first `?n := ?m t`.
       Reason: this assignment is precise. -/
    condM (commitWhen (processAssignment s t)) (pure LBool.true) $
    assign t s
  else
    condM (commitWhen (processAssignment t s)) (pure LBool.true) $
    assign s t

@[inline] def whenUndefDo (x : MetaM LBool) (k : MetaM Bool) : MetaM Bool := do
status ← x;
match status with
| LBool.true  => pure true
| LBool.false => pure false
| LBool.undef => k

@[specialize] private partial def isDefEqWHNF
    (t s : Expr)
    (k : Expr → Expr → MetaM Bool) : MetaM Bool := do
t' ← whnfCore t;
s' ← whnfCore s;
if t == t' && s == s' then
  k t' s'
else
  whenUndefDo (isDefEqQuick t' s') $
    k t' s'

@[specialize] private def unstuckMVar
    (e : Expr)
    (successK : Expr → MetaM Bool) (failK : MetaM Bool): MetaM Bool := do
mvarId? ← getStuckMVar? e;
match mvarId? with
| some mvarId =>
  condM (synthPending mvarId)
    (do e ← instantiateMVars e; successK e)
    failK
| none   => failK

private def isDefEqOnFailure (t s : Expr) : MetaM Bool :=
unstuckMVar t (fun t => isExprDefEqAux t s) $
unstuckMVar s (fun s => isExprDefEqAux t s) $
pure false

/- Remove unnecessary let-decls -/
private def consumeLet : Expr → Expr
| e@(Expr.letE _ _ _ b _) => if b.hasLooseBVars then e else consumeLet b
| e                       => e

partial def isExprDefEqAuxImpl : Expr → Expr → MetaM Bool
| t, s => do
  let t := consumeLet t;
  let s := consumeLet s;
  trace `Meta.isDefEq.step $ fun _ => t ++ " =?= " ++ s;
  whenUndefDo (isDefEqQuick t s) $
  whenUndefDo (isDefEqProofIrrel t s) $
  isDefEqWHNF t s $ fun t s => do
  condM (isDefEqEta t s <||> isDefEqEta s t) (pure true) $
  whenUndefDo (isDefEqNative t s) $ do
  whenUndefDo (isDefEqNat t s) $ do
  whenUndefDo (isDefEqOffset t s) $ do
  whenUndefDo (isDefEqDelta t s) $
  match t, s with
  | Expr.const c us _, Expr.const d vs _ => if c == d then isListLevelDefEqAux us vs else pure false
  | Expr.app _ _ _,    Expr.app _ _ _    =>
    let tFn := t.getAppFn;
    condM (commitWhen (isExprDefEqAux tFn s.getAppFn <&&> isDefEqArgs tFn t.getAppArgs s.getAppArgs))
      (pure true)
      (isDefEqOnFailure t s)
  | _, _ =>
    whenUndefDo (isDefEqStringLit t s) $
    isDefEqOnFailure t s

@[init] def setIsExprDefEqAuxRef : IO Unit :=
isExprDefEqAuxRef.set isExprDefEqAuxImpl

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Meta.isDefEq;
registerTraceClass `Meta.isDefEq.foApprox;
registerTraceClass `Meta.isDefEq.delta;
registerTraceClass `Meta.isDefEq.step;
registerTraceClass `Meta.isDefEq.assign

end Meta
end Lean
