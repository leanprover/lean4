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
| functionExpected (e : Expr) (f : Expr) (fType : Expr)
| unknownConstant (name : Name)
| incorrectNumberOfLevels (e : Expr)
-- TODO: add remaining errors

@[specialize] private def inferAppType {m : Type → Type} [Monad m] [MonadExcept InferTypeException m]
    (whnf      : Expr → m Expr)
    (inferType : Expr → m Expr)
    (f : Expr) (args : Array Expr) : m Expr :=
do fType ← inferType f;
   (j, fType) ← args.size.foldM
     (fun i (acc : Nat × Expr) =>
       let (j, fType) := acc;
       match fType with
       | Expr.forallE _ _ _ b => pure (j, b)
       | _ => do
         fType ← whnf $ fType.instantiateRevRange j i args;
         match fType with
         | Expr.forallE _ _ _ b => pure (i, b)
         | _ => throw $ InferTypeException.functionExpected (mkApp f args) f fType)
     (0, fType);
   pure $ fType.instantiateRevRange j args.size args

def inferConstType {m : Type → Type} [Monad m] [MonadExcept InferTypeException m]
    (env : Environment) (c : Name) (lvls : List Level) : m Expr :=
match env.find c with
| some cinfo =>
  if cinfo.lparams.length == lvls.length then
    throw $ InferTypeException.incorrectNumberOfLevels (Expr.const c lvls)
  else
    pure $ cinfo.instantiateTypeLevelParams lvls
| none       => throw $ InferTypeException.unknownConstant c

-- TODO

end Lean
