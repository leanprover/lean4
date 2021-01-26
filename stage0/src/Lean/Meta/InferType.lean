/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.LBool
import Lean.Meta.Basic

namespace Lean

/-
Auxiliary function for instantiating the loose bound variables in `e` with `args[start:stop]`.
This function is similar to `instantiateRevRange`, but it applies beta-reduction when
we instantiate a bound variable with a lambda expression.
Example: Given the term `#0 a`, and `start := 0, stop := 1, args := #[fun x => x]` the result is
`a` instead of `(fun x => x) a`.
This reduction is useful when we are inferring the type of eliminator-like applications.
For example, given `(n m : Nat) (f : Nat → Nat) (h : m = n)`,
the type of `Eq.subst (motive := fun x => f m = f x) h rfl`
is `motive n` which is `(fun (x : Nat) => f m = f x) n`
This function reduces the new application to `f m = f n`

We use it to implement `inferAppType`
-/
partial def Expr.instantiateBetaRevRange (e : Expr) (start : Nat) (stop : Nat) (args : Array Expr) : Expr :=
  if e.hasLooseBVars && stop > start then
    assert! stop ≤ args.size
    visit e 0 |>.run
  else
    e
where
  visit (e : Expr) (offset : Nat) : MonadStateCacheT (Expr × Nat) Expr Id Expr :=
    if offset >= e.looseBVarRange then
      -- `e` doesn't have free variables
      return e
    else checkCache (e, offset) fun _ => do
      match e with
      | Expr.forallE _ d b _   => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
      | Expr.lam _ d b _       => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
      | Expr.letE _ t v b _    => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
      | Expr.mdata _ b _       => return e.updateMData! (← visit b offset)
      | Expr.proj _ _ b _      => return e.updateProj! (← visit b offset)
      | Expr.app f a _         =>
        e.withAppRev fun f revArgs => do
        let fNew    ← visit f offset
        let revArgs ← revArgs.mapM (visit · offset)
        if f.isBVar then
          -- try to beta reduce if `f` was a bound variable
          return fNew.betaRev revArgs
        else
          return mkAppRev fNew revArgs
      | Expr.bvar vidx _       =>
        -- Recall that looseBVarRange for `Expr.bvar` is `vidx+1`.
        -- So, we must have offset ≤ vidx, since we are in the "else" branch of  `if offset >= e.looseBVarRange`
        let n := stop - start
        if vidx < offset + n then
          return args[stop - (vidx - offset) - 1].liftLooseBVars 0 offset
        else
          return mkBVar (vidx - n)
      -- The following cases are unreachable because they never contain loose bound variables
      | Expr.const .. => unreachable!
      | Expr.fvar ..  => unreachable!
      | Expr.mvar ..  => unreachable!
      | Expr.sort ..  => unreachable!
      | Expr.lit ..   => unreachable!

namespace Meta

def throwFunctionExpected {α} (f : Expr) : MetaM α :=
  throwError! "function expected{indentExpr f}"

private def inferAppType (f : Expr) (args : Array Expr) : MetaM Expr := do
  let mut fType ← inferType f
  let mut j := 0
  /- TODO: check whether `instantiateBetaRevRange` is too expensive, and
     use it only when `args` contains a lambda expression. -/
  for i in [:args.size] do
    match fType with
    | Expr.forallE _ _ b _ => fType := b
    | _ =>
      match (← whnf <| fType.instantiateBetaRevRange j i args) with
      | Expr.forallE _ _ b _ => j := i; fType := b
      | _ => throwFunctionExpected <| mkAppRange f 0 (i+1) args
  return fType.instantiateBetaRevRange j args.size args

def throwIncorrectNumberOfLevels {α} (constName : Name) (us : List Level) : MetaM α :=
  throwError! "incorrect number of universe levels {mkConst constName us}"

private def inferConstType (c : Name) (us : List Level) : MetaM Expr := do
  let cinfo ← getConstInfo c
  if cinfo.lparams.length == us.length then
    pure $ cinfo.instantiateTypeLevelParams us
  else
    throwIncorrectNumberOfLevels c us

private def inferProjType (structName : Name) (idx : Nat) (e : Expr) : MetaM Expr := do
  let failed {α} : Unit → MetaM α := fun _ =>
    throwError! "invalid projection{indentExpr (mkProj structName idx e)}"
  let structType ← inferType e
  let structType ← whnf structType
  matchConstStruct structType.getAppFn failed fun structVal structLvls ctorVal =>
    let n := structVal.numParams
    let structParams := structType.getAppArgs
    if n != structParams.size then failed ()
    else do
      let mut ctorType ← inferAppType (mkConst ctorVal.name structLvls) structParams
      for i in [:idx] do
        ctorType ← whnf ctorType
        match ctorType with
        | Expr.forallE _ _ body _ =>
          if body.hasLooseBVars then
            ctorType := body.instantiate1 $ mkProj structName i e
          else
            ctorType := body
        | _ => failed ()
      ctorType ← whnf ctorType
      match ctorType with
      | Expr.forallE _ d _ _ => pure d
      | _                    => failed ()

def throwTypeExcepted {α} (type : Expr) : MetaM α :=
  throwError! "type expected{indentExpr type}"

def getLevel (type : Expr) : MetaM Level := do
  let typeType ← inferType type
  let typeType ← whnfD typeType
  match typeType with
  | Expr.sort lvl _    => pure lvl
  | Expr.mvar mvarId _ =>
    if (← isReadOnlyOrSyntheticOpaqueExprMVar mvarId) then
      throwTypeExcepted type
    else
      let lvl ← mkFreshLevelMVar
      assignExprMVar mvarId (mkSort lvl)
      pure lvl
  | _ => throwTypeExcepted type

private def inferForallType (e : Expr) : MetaM Expr :=
  forallTelescope e fun xs e => do
    let lvl  ← getLevel e
    let lvl  ← xs.foldrM (init := lvl) fun x lvl => do
      let xType    ← inferType x
      let xTypeLvl ← getLevel xType
      pure $ mkLevelIMax' xTypeLvl lvl
    pure $ mkSort lvl.normalize

/- Infer type of lambda and let expressions -/
private def inferLambdaType (e : Expr) : MetaM Expr :=
  lambdaLetTelescope e fun xs e => do
    let type ← inferType e
    mkForallFVars xs type

@[inline] private def withLocalDecl' {α} (name : Name) (bi : BinderInfo) (type : Expr) (x : Expr → MetaM α) : MetaM α :=
  savingCache do
    let fvarId ← mkFreshId
    withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarId name type bi }) do
      x (mkFVar fvarId)

def throwUnknownMVar {α} (mvarId : MVarId) : MetaM α :=
  throwError! "unknown metavariable '{mkMVar mvarId}'"

private def inferMVarType (mvarId : MVarId) : MetaM Expr := do
  match (← getMCtx).findDecl? mvarId with
  | some d => pure d.type
  | none   => throwUnknownMVar mvarId

private def inferFVarType (fvarId : FVarId) : MetaM Expr := do
  match (← getLCtx).find? fvarId with
  | some d => pure d.type
  | none   => throwUnknownFVar fvarId

@[inline] private def checkInferTypeCache (e : Expr) (inferType : MetaM Expr) : MetaM Expr := do
  match (← get).cache.inferType.find? e with
  | some type => pure type
  | none =>
    let type ← inferType
    modify fun s => { s with cache := { s.cache with inferType := s.cache.inferType.insert e type } }
    pure type

def inferTypeImp (e : Expr) : MetaM Expr :=
  let rec infer : Expr → MetaM Expr
    | Expr.const c lvls _      => inferConstType c lvls
    | e@(Expr.proj n i s _)    => checkInferTypeCache e (inferProjType n i s)
    | e@(Expr.app f _ _)       => checkInferTypeCache e (inferAppType f.getAppFn e.getAppArgs)
    | Expr.mvar mvarId _       => inferMVarType mvarId
    | Expr.fvar fvarId _       => inferFVarType fvarId
    | Expr.bvar bidx _         => throwError! "unexpected bound variable {mkBVar bidx}"
    | Expr.mdata _ e _         => infer e
    | Expr.lit v _             => pure v.type
    | Expr.sort lvl _          => pure $ mkSort (mkLevelSucc lvl)
    | e@(Expr.forallE _ _ _ _) => checkInferTypeCache e (inferForallType e)
    | e@(Expr.lam _ _ _ _)     => checkInferTypeCache e (inferLambdaType e)
    | e@(Expr.letE _ _ _ _ _)  => checkInferTypeCache e (inferLambdaType e)
  withTransparency TransparencyMode.default (infer e)

@[builtinInit] def setInferTypeRef : IO Unit :=
inferTypeRef.set inferTypeImp

/--
  Return `LBool.true` if given level is always equivalent to universe level zero.
  It is used to implement `isProp`. -/
private def isAlwaysZero : Level → Bool
  | Level.zero _     => true
  | Level.mvar _ _   => false
  | Level.param _ _  => false
  | Level.succ _ _   => false
  | Level.max u v _  => isAlwaysZero u && isAlwaysZero v
  | Level.imax _ u _ => isAlwaysZero u

/--
  `isArrowProp type n` is an "approximate" predicate which returns `LBool.true`
   if `type` is of the form `A_1 -> ... -> A_n -> Prop`.
   Remark: `type` can be a dependent arrow. -/
private partial def isArrowProp : Expr → Nat → MetaM LBool
  | Expr.sort u _,        0   => return isAlwaysZero (← instantiateLevelMVars u) |>.toLBool
  | Expr.forallE _ _ _ _, 0   => pure LBool.false
  | Expr.forallE _ _ b _, n+1 => isArrowProp b n
  | Expr.letE _ _ _ b _,  n   => isArrowProp b n
  | Expr.mdata _ e _,     n   => isArrowProp e n
  | _,                    _   => pure LBool.undef

/--
  `isPropQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a proposition. -/
private partial def isPropQuickApp : Expr → Nat → MetaM LBool
  | Expr.const c lvls _, arity   => do let constType ← inferConstType c lvls; isArrowProp constType arity
  | Expr.fvar fvarId _,  arity   => do let fvarType  ← inferFVarType fvarId;  isArrowProp fvarType arity
  | Expr.mvar mvarId _,  arity   => do let mvarType  ← inferMVarType mvarId;  isArrowProp mvarType arity
  | Expr.app f _ _,      arity   => isPropQuickApp f (arity+1)
  | Expr.mdata _ e _,    arity   => isPropQuickApp e arity
  | Expr.letE _ _ _ b _, arity   => isPropQuickApp b arity
  | Expr.lam _ _ _ _,    0       => pure LBool.false
  | Expr.lam _ _ b _,    arity+1 => isPropQuickApp b arity
  | _,                   _       => pure LBool.undef

/--
  `isPropQuick e` is an "approximate" predicate which returns `LBool.true`
  if `e` is a proposition. -/
partial def isPropQuick : Expr → MetaM LBool
  | Expr.bvar _ _         => pure LBool.undef
  | Expr.lit _ _          => pure LBool.false
  | Expr.sort _ _         => pure LBool.false
  | Expr.lam _ _ _ _      => pure LBool.false
  | Expr.letE _ _ _ b _   => isPropQuick b
  | Expr.proj _ _ _ _     => pure LBool.undef
  | Expr.forallE _ _ b _  => isPropQuick b
  | Expr.mdata _ e _      => isPropQuick e
  | Expr.const c lvls _   => do let constType ← inferConstType c lvls; isArrowProp constType 0
  | Expr.fvar fvarId _    => do let fvarType  ← inferFVarType fvarId;  isArrowProp fvarType 0
  | Expr.mvar mvarId _    => do let mvarType  ← inferMVarType mvarId;  isArrowProp mvarType 0
  | Expr.app f _ _        => isPropQuickApp f 1

/-- `isProp whnf e` return `true` if `e` is a proposition.

     If `e` contains metavariables, it may not be possible
     to decide whether is a proposition or not. We return `false` in this
     case. We considered using `LBool` and retuning `LBool.undef`, but
     we have no applications for it. -/
def isProp (e : Expr) : MetaM Bool := do
  let r ← isPropQuick e
  match r with
  | LBool.true  => pure true
  | LBool.false => pure false
  | LBool.undef =>
    let type ← inferType e
    let type ← whnfD type
    match type with
    | Expr.sort u _ => return isAlwaysZero (← instantiateLevelMVars u)
    | _             => pure false

/--
  `isArrowProposition type n` is an "approximate" predicate which returns `LBool.true`
   if `type` is of the form `A_1 -> ... -> A_n -> B`, where `B` is a proposition.
   Remark: `type` can be a dependent arrow. -/
private partial def isArrowProposition : Expr → Nat → MetaM LBool
  | Expr.forallE _ _ b _, n+1 => isArrowProposition b n
  | Expr.letE _ _ _ b _,  n   => isArrowProposition b n
  | Expr.mdata _ e _,     n   => isArrowProposition e n
  | type,                 0   => isPropQuick type
  | _,                    _   => pure LBool.undef

mutual
/--
  `isProofQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a proof. -/
private partial def isProofQuickApp : Expr → Nat → MetaM LBool
  | Expr.const c lvls _, arity   => do let constType ← inferConstType c lvls; isArrowProposition constType arity
  | Expr.fvar fvarId _,  arity   => do let fvarType  ← inferFVarType fvarId;  isArrowProposition fvarType arity
  | Expr.mvar mvarId _,  arity   => do let mvarType  ← inferMVarType mvarId;  isArrowProposition mvarType arity
  | Expr.app f _ _,      arity   => isProofQuickApp f (arity+1)
  | Expr.mdata _ e _,    arity   => isProofQuickApp e arity
  | Expr.letE _ _ _ b _, arity   => isProofQuickApp b arity
  | Expr.lam _ _ b _,    0       => isProofQuick b
  | Expr.lam _ _ b _,    arity+1 => isProofQuickApp b arity
  | _,                   _       => pure LBool.undef

/--
  `isProofQuick e` is an "approximate" predicate which returns `LBool.true`
  if `e` is a proof. -/
partial def isProofQuick : Expr → MetaM LBool
  | Expr.bvar _ _         => pure LBool.undef
  | Expr.lit _ _          => pure LBool.false
  | Expr.sort _ _         => pure LBool.false
  | Expr.lam _ _ b _      => isProofQuick b
  | Expr.letE _ _ _ b _   => isProofQuick b
  | Expr.proj _ _ _ _     => pure LBool.undef
  | Expr.forallE _ _ b _  => pure LBool.false
  | Expr.mdata _ e _      => isProofQuick e
  | Expr.const c lvls _   => do let constType ← inferConstType c lvls; isArrowProposition constType 0
  | Expr.fvar fvarId _    => do let fvarType  ← inferFVarType fvarId;  isArrowProposition fvarType 0
  | Expr.mvar mvarId _    => do let mvarType  ← inferMVarType mvarId;  isArrowProposition mvarType 0
  | Expr.app f _ _        => isProofQuickApp f 1

end

def isProof (e : Expr) : MetaM Bool := do
  let r ← isProofQuick e
  match r with
  | LBool.true  => pure true
  | LBool.false => pure false
  | LBool.undef => do
    let type ← inferType e
    Meta.isProp type

/--
  `isArrowType type n` is an "approximate" predicate which returns `LBool.true`
   if `type` is of the form `A_1 -> ... -> A_n -> Sort _`.
   Remark: `type` can be a dependent arrow. -/
private partial def isArrowType : Expr → Nat → MetaM LBool
  | Expr.sort u _,        0   => pure LBool.true
  | Expr.forallE _ _ _ _, 0   => pure LBool.false
  | Expr.forallE _ _ b _, n+1 => isArrowType b n
  | Expr.letE _ _ _ b _,  n   => isArrowType b n
  | Expr.mdata _ e _,     n   => isArrowType e n
  | _,                    _   => pure LBool.undef

/--
  `isTypeQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a type. -/
private partial def isTypeQuickApp : Expr → Nat → MetaM LBool
  | Expr.const c lvls _, arity   => do let constType ← inferConstType c lvls; isArrowType constType arity
  | Expr.fvar fvarId _,  arity   => do let fvarType  ← inferFVarType fvarId;  isArrowType fvarType arity
  | Expr.mvar mvarId _,  arity   => do let mvarType  ← inferMVarType mvarId;  isArrowType mvarType arity
  | Expr.app f _ _,      arity   => isTypeQuickApp f (arity+1)
  | Expr.mdata _ e _,    arity   => isTypeQuickApp e arity
  | Expr.letE _ _ _ b _, arity   => isTypeQuickApp b arity
  | Expr.lam _ _ _ _,    0       => pure LBool.false
  | Expr.lam _ _ b _,    arity+1 => isTypeQuickApp b arity
  | _,                   _       => pure LBool.undef

/--
  `isTypeQuick e` is an "approximate" predicate which returns `LBool.true`
  if `e` is a type. -/
partial def isTypeQuick : Expr → MetaM LBool
  | Expr.bvar _ _         => pure LBool.undef
  | Expr.lit _ _          => pure LBool.false
  | Expr.sort _ _         => pure LBool.true
  | Expr.lam _ _ _ _      => pure LBool.false
  | Expr.letE _ _ _ b _   => isTypeQuick b
  | Expr.proj _ _ _ _     => pure LBool.undef
  | Expr.forallE _ _ b _  => pure LBool.true
  | Expr.mdata _ e _      => isTypeQuick e
  | Expr.const c lvls _   => do let constType ← inferConstType c lvls; isArrowType constType 0
  | Expr.fvar fvarId _    => do let fvarType  ← inferFVarType fvarId;  isArrowType fvarType 0
  | Expr.mvar mvarId _    => do let mvarType  ← inferMVarType mvarId;  isArrowType mvarType 0
  | Expr.app f _ _        => isTypeQuickApp f 1

def isType (e : Expr) : MetaM Bool := do
  let r ← isTypeQuick e
  match r with
  | LBool.true  => pure true
  | LBool.false => pure false
  | LBool.undef =>
    let type ← inferType e
    let type ← whnfD type
    match type with
    | Expr.sort _ _ => pure true
    | _             => pure false

partial def isTypeFormerType (type : Expr) : MetaM Bool := do
  let type ← whnfD type
  match type with
  | Expr.sort _ _ => pure true
  | Expr.forallE n d b c =>
    withLocalDecl' n c.binderInfo d fun fvar =>
    isTypeFormerType (b.instantiate1 fvar)
  | _ => pure false

/--
  Return true iff `e : Sort _` or `e : (forall As, Sort _)`.
  Remark: it subsumes `isType` -/
def isTypeFormer (e : Expr) : MetaM Bool := do
  let type ← inferType e
  isTypeFormerType type

end Lean.Meta
