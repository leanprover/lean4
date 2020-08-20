/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.LBool
import Lean.Meta.Basic

namespace Lean
namespace Meta

def throwFunctionExpected {α} (f : Expr) : MetaM α :=
throwError $ "function expected " ++ f

private def inferAppType (f : Expr) (args : Array Expr) : MetaM Expr := do
fType ← inferType f;
(j, fType) ← args.size.foldM
  (fun i (acc : Nat × Expr) =>
    let (j, type) := acc;
    match type with
    | Expr.forallE _ _ b _ => pure (j, b)
    | _ => do
      type ← whnf $ type.instantiateRevRange j i args;
      match type with
      | Expr.forallE _ _ b _ => pure (i, b)
      | _ => throwFunctionExpected $ mkAppRange f 0 (i+1) args)
  (0, fType);
pure $ fType.instantiateRevRange j args.size args

def throwIncorrectNumberOfLevels {α} (constName : Name) (us : List Level) : MetaM α :=
throwError $ "incorrect number of universe levels " ++ mkConst constName us

private def inferConstType (c : Name) (us : List Level) : MetaM Expr := do
env ← getEnv;
match env.find? c with
| some cinfo =>
  if cinfo.lparams.length == us.length then
    pure $ cinfo.instantiateTypeLevelParams us
  else
    throwIncorrectNumberOfLevels c us
| none =>
  throwUnknownConstant c

private def inferProjType (structName : Name) (idx : Nat) (e : Expr) : MetaM Expr := do
let failed : Unit → MetaM Expr := fun _ => throwError $ "invalide projection" ++ indentExpr (mkProj structName idx e);
structType ← inferType e;
structType ← whnf structType;
env ← getEnv;
matchConst env structType.getAppFn failed $ fun structInfo structLvls => do
  match structInfo with
  | ConstantInfo.inductInfo { nparams := n, ctors := [ctor], .. } =>
    let structParams := structType.getAppArgs;
    if n != structParams.size then failed ()
    else match env.find? ctor with
      | none            => failed ()
      | some (ctorInfo) => do
        ctorType ← inferAppType (mkConst ctor structLvls) structParams;
        ctorType ← idx.foldM
          (fun i ctorType => do
            ctorType ← whnf ctorType;
            match ctorType with
            | Expr.forallE _ _ body _ =>
              if body.hasLooseBVars then
                pure $ body.instantiate1 $ mkProj structName i e
              else
                pure body
            | _ => failed ())
          ctorType;
        ctorType ← whnf ctorType;
        match ctorType with
        | Expr.forallE _ d _ _ => pure d
        | _                    => failed ()
  | _ => failed ()

def throwTypeExcepted {α} (type : Expr) : MetaM α :=
throwError $ "type expected " ++ indentExpr type

def getLevel (type : Expr) : MetaM Level := do
typeType ← inferType type;
typeType ← whnfD typeType;
match typeType with
| Expr.sort lvl _    => pure lvl
| Expr.mvar mvarId _ =>
  condM (isReadOnlyOrSyntheticOpaqueExprMVar mvarId)
    (throwTypeExcepted type)
    (do lvl ← mkFreshLevelMVar;
        assignExprMVar mvarId (mkSort lvl);
        pure lvl)
| _ => throwTypeExcepted type

private def inferForallType (e : Expr) : MetaM Expr :=
forallTelescope e $ fun xs e => do
  lvl  ← getLevel e;
  lvl  ← xs.foldrM
    (fun x lvl => do
      xType    ← inferType x;
      xTypeLvl ← getLevel xType;
      pure $ mkLevelIMax xTypeLvl lvl)
    lvl;
  pure $ mkSort lvl.normalize

/- Infer type of lambda and let expressions -/
private def inferLambdaType (e : Expr) : MetaM Expr :=
lambdaTelescope e $ fun xs e => do
  type ← inferType e;
  mkForall xs type

@[inline] private def withLocalDecl {α} (name : Name) (bi : BinderInfo) (type : Expr) (x : Expr → MetaM α) : MetaM α :=
savingCache $ do
  fvarId ← mkFreshId;
  adaptReader (fun (ctx : Context) => { ctx with lctx := ctx.lctx.mkLocalDecl fvarId name type bi }) $
    x (mkFVar fvarId)

def throwUnknownMVar {α} (mvarId : MVarId) : MetaM α :=
throwError $ "unknown metavariable '" ++ mkMVar mvarId ++ "'"

private def inferMVarType (mvarId : MVarId) : MetaM Expr := do
mctx ← getMCtx;
match mctx.findDecl? mvarId with
| some d => pure d.type
| none   => throwUnknownMVar mvarId

private def inferFVarType (fvarId : FVarId) : MetaM Expr := do
lctx ← getLCtx;
match lctx.find? fvarId with
| some d => pure d.type
| none   => throwUnknownFVar fvarId

@[inline] private def checkInferTypeCache (e : Expr) (inferType : MetaM Expr) : MetaM Expr := do
s ← get;
match s.cache.inferType.find? e with
| some type => pure type
| none => do
  type ← inferType;
  modify $ fun s => { s with cache := { s.cache with inferType := s.cache.inferType.insert e type } };
  pure type

private partial def inferTypeAux : Expr → MetaM Expr
| Expr.const c lvls _      => inferConstType c lvls
| e@(Expr.proj n i s _)    => checkInferTypeCache e (inferProjType n i s)
| e@(Expr.app f _ _)       => checkInferTypeCache e (inferAppType f.getAppFn e.getAppArgs)
| Expr.mvar mvarId _       => inferMVarType mvarId
| Expr.fvar fvarId _       => inferFVarType fvarId
| Expr.bvar bidx _         => throwError $ "unexpected bound variable " ++ mkBVar bidx
| Expr.mdata _ e _         => inferTypeAux e
| Expr.lit v _             => pure v.type
| Expr.sort lvl _          => pure $ mkSort (mkLevelSucc lvl)
| e@(Expr.forallE _ _ _ _) => checkInferTypeCache e (inferForallType e)
| e@(Expr.lam _ _ _ _)     => checkInferTypeCache e (inferLambdaType e)
| e@(Expr.letE _ _ _ _ _)  => checkInferTypeCache e (inferLambdaType e)
| Expr.localE _ _ _ _      => unreachable!

def inferTypeImpl (e : Expr) : MetaM Expr :=
withTransparency TransparencyMode.default (inferTypeAux e)

@[init] def setInferTypeRef : IO Unit :=
inferTypeRef.set inferTypeImpl

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
| Expr.sort u _,        0   => do u ← instantiateLevelMVars u; pure $ (isAlwaysZero u).toLBool
| Expr.forallE _ _ _ _, 0   => pure LBool.false
| Expr.forallE _ _ b _, n+1 => isArrowProp b n
| Expr.letE _ _ _ b _,  n   => isArrowProp b n
| Expr.mdata _ e _,     n   => isArrowProp e n
| _,                    _   => pure LBool.undef

/--
  `isPropQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a proposition. -/
private partial def isPropQuickApp : Expr → Nat → MetaM LBool
| Expr.const c lvls _, arity   => do constType ← inferConstType c lvls; isArrowProp constType arity
| Expr.fvar fvarId _,  arity   => do fvarType  ← inferFVarType fvarId;  isArrowProp fvarType arity
| Expr.mvar mvarId _,  arity   => do mvarType  ← inferMVarType mvarId;  isArrowProp mvarType arity
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
| Expr.const c lvls _   => do constType ← inferConstType c lvls; isArrowProp constType 0
| Expr.fvar fvarId _    => do fvarType  ← inferFVarType fvarId;  isArrowProp fvarType 0
| Expr.mvar mvarId _    => do mvarType  ← inferMVarType mvarId;  isArrowProp mvarType 0
| Expr.app f _ _        => isPropQuickApp f 1
| Expr.localE _ _ _ _   => unreachable!

/-- `isProp whnf e` return `true` if `e` is a proposition.

     If `e` contains metavariables, it may not be possible
     to decide whether is a proposition or not. We return `false` in this
     case. We considered using `LBool` and retuning `LBool.undef`, but
     we have no applications for it. -/
def isProp (e : Expr) : MetaM Bool := do
r ← isPropQuick e;
match r with
| LBool.true  => pure true
| LBool.false => pure false
| LBool.undef => do
  -- dbgTrace ("isPropQuick failed " ++ toString e);
  type ← inferType e;
  type ← whnfD type;
  match type with
  | Expr.sort u _ => do u ← instantiateLevelMVars u; pure $ isAlwaysZero u
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

/--
  `isProofQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a proof. -/
@[specialize] private partial def isProofQuickApp (isProofQuick : Expr → MetaM LBool) : Expr → Nat → MetaM LBool
| Expr.const c lvls _, arity   => do constType ← inferConstType c lvls; isArrowProposition constType arity
| Expr.fvar fvarId _,  arity   => do fvarType  ← inferFVarType fvarId;  isArrowProposition fvarType arity
| Expr.mvar mvarId _,  arity   => do mvarType  ← inferMVarType mvarId;  isArrowProposition mvarType arity
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
| Expr.const c lvls _   => do constType ← inferConstType c lvls; isArrowProposition constType 0
| Expr.fvar fvarId _    => do fvarType  ← inferFVarType fvarId;  isArrowProposition fvarType 0
| Expr.mvar mvarId _    => do mvarType  ← inferMVarType mvarId;  isArrowProposition mvarType 0
| Expr.app f _ _        => isProofQuickApp isProofQuick f 1
| Expr.localE _ _ _ _   => unreachable!

def isProof (e : Expr) : MetaM Bool := do
r ← isProofQuick e;
match r with
| LBool.true  => pure true
| LBool.false => pure false
| LBool.undef => do
  type ← inferType e;
  isProp type

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
| Expr.const c lvls _, arity   => do constType ← inferConstType c lvls; isArrowType constType arity
| Expr.fvar fvarId _,  arity   => do fvarType  ← inferFVarType fvarId;  isArrowType fvarType arity
| Expr.mvar mvarId _,  arity   => do mvarType  ← inferMVarType mvarId;  isArrowType mvarType arity
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
| Expr.const c lvls _   => do constType ← inferConstType c lvls; isArrowType constType 0
| Expr.fvar fvarId _    => do fvarType  ← inferFVarType fvarId;  isArrowType fvarType 0
| Expr.mvar mvarId _    => do mvarType  ← inferMVarType mvarId;  isArrowType mvarType 0
| Expr.app f _ _        => isTypeQuickApp f 1
| Expr.localE _ _ _ _   => unreachable!

def isType (e : Expr) : MetaM Bool := do
r ← isTypeQuick e;
match r with
| LBool.true  => pure true
| LBool.false => pure false
| LBool.undef => do
  type ← inferType e;
  type ← whnfD type;
  match type with
  | Expr.sort _ _ => pure true
  | _             => pure false

partial def isTypeFormerType : Expr → MetaM Bool
| type => do
  type ← whnfD type;
  match type with
  | Expr.sort _ _ => pure true
  | Expr.forallE n d b c =>
    withLocalDecl n d c.binderInfo $ fun fvar =>
    isTypeFormerType (b.instantiate1 fvar)
  | _ => pure false

/--
  Return true iff `e : Sort _` or `e : (forall As, Sort _)`.
  Remark: it subsumes `isType` -/
def isTypeFormer (e : Expr) : MetaM Bool := do
type ← inferType e;
isTypeFormerType type

end Meta
end Lean
