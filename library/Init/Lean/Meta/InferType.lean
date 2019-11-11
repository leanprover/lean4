/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
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
       | Expr.forallE _ _ _ b => pure (j, b)
       | _ => do
         type ← whnf $ type.instantiateRevRange j i args;
         match type with
         | Expr.forallE _ _ _ b => pure (i, b)
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
       throwEx $ Exception.incorrectNumOfLevels c lvls
     else
       pure $ cinfo.instantiateTypeLevelParams lvls
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
               | Expr.forallE _ _ _ body =>
                 if body.hasLooseBVars then
                   pure $ body.instantiate1 $ Expr.proj structName i e
                 else
                   pure body
               | _ => failed ())
             ctorType;
           ctorType ← whnf ctorType;
           match ctorType with
           | Expr.forallE _ _ d _ => pure d
           | _                    => failed ()
     | _ => failed ()

@[specialize] private def getLevel
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (type : Expr) : MetaM Level :=
do typeType ← inferType type;
   typeType ← whnf type;
   match typeType with
   | Expr.sort lvl    => pure lvl
   | Expr.mvar mvarId =>
     condM (isReadOnlyOrSyntheticExprMVar mvarId)
       (throwEx $ Exception.typeExpected type)
       (do levelMVarId ← mkFreshId;
           let lvl := Level.mvar levelMVarId;
           assignExprMVar mvarId (Expr.sort lvl);
           pure lvl)
   | _ => throwEx $ Exception.typeExpected type

@[specialize] private def inferForallType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (e : Expr) : MetaM Expr :=
forallTelescope whnf e $ fun xs e => do
  type ← inferType e;
  lvl  ← getLevel whnf inferType type;
  lvl  ← xs.foldrM
    (fun x lvl => do
      xType    ← inferType x;
      xTypeLvl ← getLevel whnf inferType xType;
      pure $ Level.imax xTypeLvl lvl)
    lvl;
  pure $ Expr.sort lvl

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
    x (Expr.fvar fvarId)

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
| Expr.const c lvls        => inferConstType c lvls
| e@(Expr.proj n i s)      => checkInferTypeCache e (inferProjType whnf inferTypeAuxAux n i s)
| e@(Expr.app f _)         => checkInferTypeCache e (inferAppType whnf inferTypeAuxAux f e.getAppArgs)
| Expr.mvar mvarId         => inferMVarType mvarId
| Expr.fvar fvarId         => inferFVarType fvarId
| Expr.bvar _              => unreachable!
| Expr.mdata _ e           => inferTypeAuxAux e
| Expr.lit v               => pure v.type
| Expr.sort lvl            => pure $ Expr.sort (Level.succ lvl)
| e@(Expr.forallE _ _ _ _) => checkInferTypeCache e (inferForallType whnf inferTypeAuxAux e)
| e@(Expr.lam _ _ _ _)     => checkInferTypeCache e (inferLambdaType whnf inferTypeAuxAux e)
| e@(Expr.letE _ _ _ _)    => checkInferTypeCache e (inferLambdaType whnf inferTypeAuxAux e)

@[inline] def inferTypeAux
    (whnf : Expr → MetaM Expr)
    (e : Expr) : MetaM Expr :=
inferTypeAuxAux (fun e => usingTransparency TransparencyMode.all $ whnf e) e

@[specialize] def isPropAux
    (whnf : Expr → MetaM Expr)
    (e : Expr) : MetaM Bool :=
do type ← inferTypeAux whnf e;
   type ← whnf type;
   match type with
   | Expr.sort Level.zero => pure true
   | _                    => pure false

end Meta
end Lean
