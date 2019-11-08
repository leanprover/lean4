/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat
import Init.Lean.Declaration
import Init.Lean.LocalContext
import Init.Lean.Environment

namespace Lean

inductive InferTypeException
| functionExpected (fType : Expr) (args : Array Expr)
| unknownConstant (constName : Name)
| incorrectNumberOfLevels (constName : Name) (constLvls : List Level)
| invalidProjection (structName : Name) (idx : Nat) (s : Expr)
-- TODO: add remaining errors

@[specialize] private def getForallResultType {m : Type → Type} [Monad m] [MonadExcept InferTypeException m]
    (whnf      : Expr → m Expr)
    (fType : Expr) (args : Array Expr) : m Expr :=
do (j, fType) ← args.size.foldM
     (fun i (acc : Nat × Expr) =>
       let (j, type) := acc;
       match type with
       | Expr.forallE _ _ _ b => pure (j, b)
       | _ => do
         type ← whnf $ type.instantiateRevRange j i args;
         match type with
         | Expr.forallE _ _ _ b => pure (i, b)
         | _ => throw $ InferTypeException.functionExpected fType args)
     (0, fType);
   pure $ fType.instantiateRevRange j args.size args

@[specialize] private def inferAppType {m : Type → Type} [Monad m] [MonadExcept InferTypeException m]
    (whnf      : Expr → m Expr)
    (inferType : Expr → m Expr)
    (f : Expr) (args : Array Expr) : m Expr :=
do fType ← inferType f;
   getForallResultType whnf fType args

private def inferConstType {m : Type → Type} [Monad m] [MonadExcept InferTypeException m]
    (env : Environment) (c : Name) (lvls : List Level) : m Expr :=
match env.find c with
| some cinfo =>
  if cinfo.lparams.length == lvls.length then
    throw $ InferTypeException.incorrectNumberOfLevels c lvls
  else
    pure $ cinfo.instantiateTypeLevelParams lvls
| none       => throw $ InferTypeException.unknownConstant c

@[specialize] private def inferProjType {m : Type → Type} [Monad m] [MonadExcept InferTypeException m]
    (whnf      : Expr → m Expr)
    (inferType : Expr → m Expr)
    (env : Environment)
    (structName : Name) (idx : Nat) (e : Expr) : m Expr :=
do let failed : Unit → m Expr := fun _ => throw $ InferTypeException.invalidProjection structName idx e;
   structType ← inferType e;
   structType ← whnf structType;
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

-- TODO

end Lean
