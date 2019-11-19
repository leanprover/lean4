/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.LBool
import Init.Lean.Meta.Basic

namespace Lean
namespace Meta

@[specialize] private def getForallResultType
    (whnf      : Expr → MetaM Expr)
    (fType : Expr) (args : Array Expr) : MetaM Expr :=
do (j, fType) ← args.size.foldM
     (fun i (acc : Nat × Expr) =>
       let (j, type) := acc;
       match type with
       | Expr.forallE _ _ b _ => pure (j, b)
       | _ => do
         type ← whnf $ type.instantiateRevRange j i args;
         match type with
         | Expr.forallE _ _ b _ => pure (i, b)
         | _ => throwEx $ Exception.functionExpected fType args)
     (0, fType);
   pure $ fType.instantiateRevRange j args.size args

@[specialize] private def inferAppType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (f : Expr) (args : Array Expr) : MetaM Expr :=
do fType ← inferType f;
   getForallResultType whnf fType args

private def inferConstType (c : Name) (lvls : List Level) : MetaM Expr :=
do env ← getEnv;
   match env.find c with
   | some cinfo =>
     if cinfo.lparams.length == lvls.length then
       pure $ cinfo.instantiateTypeLevelParams lvls
     else
       throwEx $ Exception.incorrectNumOfLevels c lvls
   | none =>
     throwEx $ Exception.unknownConst c

@[specialize] private def inferProjType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (structName : Name) (idx : Nat) (e : Expr) : MetaM Expr :=
do let failed : Unit → MetaM Expr := fun _ => throwEx $ Exception.invalidProjection structName idx e;
   structType ← inferType e;
   structType ← whnf structType;
   env ← getEnv;
   matchConst env structType.getAppFn failed $ fun structInfo structLvls => do
     match structInfo with
     | ConstantInfo.inductInfo { nparams := n, ctors := [ctor], .. } =>
       let structParams := structType.getAppArgs;
       if n != structParams.size then failed ()
       else match env.find ctor with
         | none            => failed ()
         | some (ctorInfo) => do
           let ctorType := ctorInfo.instantiateTypeLevelParams structLvls;
           ctorType ← getForallResultType whnf ctorType structParams;
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

@[specialize] def getLevelAux
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (type : Expr) : MetaM Level :=
do typeType ← inferType type;
   typeType ← whnf typeType;
   match typeType with
   | Expr.sort lvl _    => pure lvl
   | Expr.mvar mvarId _ =>
     condM (isReadOnlyOrSyntheticExprMVar mvarId)
       (throwEx $ Exception.typeExpected type)
       (do levelMVarId ← mkFreshId;
           let lvl := mkLevelMVar levelMVarId;
           assignExprMVar mvarId (mkSort lvl);
           pure lvl)
   | _ => throwEx $ Exception.typeExpected type

@[specialize] private def inferForallType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (e : Expr) : MetaM Expr :=
forallTelescope whnf e $ fun xs e => do
  lvl  ← getLevelAux whnf inferType e;
  lvl  ← xs.foldrM
    (fun x lvl => do
      xType    ← inferType x;
      xTypeLvl ← getLevelAux whnf inferType xType;
      pure $ mkLevelIMax xTypeLvl lvl)
    lvl;
  pure $ mkSort lvl.normalize

/- Infer type of lambda and let expressions -/
@[specialize] private def inferLambdaType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (e : Expr) : MetaM Expr :=
lambdaTelescope whnf e $ fun xs e => do
  type ← inferType e;
  mkForall xs type

@[inline] private def withLocalDecl {α} (name : Name) (bi : BinderInfo) (type : Expr) (x : Expr → MetaM α) : MetaM α :=
savingCache $ do
  fvarId ← mkFreshId;
  adaptReader (fun (ctx : Context) => { lctx := ctx.lctx.mkLocalDecl fvarId name type bi, .. ctx }) $
    x (mkFVar fvarId)

private def inferMVarType (mvarId : Name) : MetaM Expr :=
do mctx ← getMCtx;
   match mctx.findDecl mvarId with
   | some d => pure d.type
   | none   => throwEx $ Exception.unknownExprMVar mvarId

private def inferFVarType (fvarId : Name) : MetaM Expr :=
do lctx ← getLCtx;
   match lctx.find fvarId with
   | some d => pure d.type
   | none   => throwEx $ Exception.unknownFVar fvarId

@[inline] private def checkInferTypeCache (e : Expr) (inferType : MetaM Expr) : MetaM Expr :=
do s ← get;
   match s.cache.inferType.find e with
   | some type => pure type
   | none => do
     type ← inferType;
     modify $ fun s => { cache := { inferType := s.cache.inferType.insert e type, .. s.cache }, .. s };
     pure type

@[specialize] partial def inferTypeAuxAux
    (whnf : Expr → MetaM Expr)
    : Expr → MetaM Expr
| Expr.const c lvls _      => inferConstType c lvls
| e@(Expr.proj n i s _)    => checkInferTypeCache e (inferProjType whnf inferTypeAuxAux n i s)
| e@(Expr.app f _ _)       => checkInferTypeCache e (inferAppType whnf inferTypeAuxAux f.getAppFn e.getAppArgs)
| Expr.mvar mvarId _       => inferMVarType mvarId
| Expr.fvar fvarId _       => inferFVarType fvarId
| Expr.bvar bidx _         => throw $ Exception.unexpectedBVar bidx
| Expr.mdata _ e _         => inferTypeAuxAux e
| Expr.lit v _             => pure v.type
| Expr.sort lvl _          => pure $ mkSort (mkLevelSucc lvl)
| e@(Expr.forallE _ _ _ _) => checkInferTypeCache e (inferForallType whnf inferTypeAuxAux e)
| e@(Expr.lam _ _ _ _)     => checkInferTypeCache e (inferLambdaType whnf inferTypeAuxAux e)
| e@(Expr.letE _ _ _ _ _)  => checkInferTypeCache e (inferLambdaType whnf inferTypeAuxAux e)
| Expr.localE _ _ _ _      => unreachable!

@[inline] def inferTypeAux
    (whnf : Expr → MetaM Expr)
    (e : Expr) : MetaM Expr :=
inferTypeAuxAux (usingDefault whnf) e

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
@[specialize] private partial def isArrowProp : Expr → Nat → MetaM LBool
| Expr.sort u _,        0   => do u ← instantiateLevelMVars u; pure $ (isAlwaysZero u).toLBool
| Expr.forallE _ _ _ _, 0   => pure LBool.false
| Expr.forallE _ _ b _, n+1 => isArrowProp b n
| Expr.letE _ _ _ b _,  n   => isArrowProp b n
| Expr.mdata _ e _,     n   => isArrowProp e n
| _,                    _   => pure LBool.undef

/--
  `isPropQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a proposition. -/
@[specialize] private partial def isPropQuickApp : Expr → Nat → MetaM LBool
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
@[specialize] private partial def isPropQuick : Expr → MetaM LBool
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
@[specialize] def isPropAux (whnf : Expr → MetaM Expr) (e : Expr) : MetaM Bool :=
do r ← isPropQuick e;
   match r with
   | LBool.true  => pure true
   | LBool.false => pure false
   | LBool.undef => do
     -- dbgTrace ("PropQuick failed " ++ toString e);
     type ← inferTypeAux whnf e;
     type ← usingDefault whnf type;
     match type with
     | Expr.sort u _ => do u ← instantiateLevelMVars u; pure $ isAlwaysZero u
     | _             => pure false

end Meta
end Lean
