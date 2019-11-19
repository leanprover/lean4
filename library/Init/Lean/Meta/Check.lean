/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.InferType

/-
This is not the Kernel type checker, but an auxiliary method for checking
whether terms produced by tactics and `isDefEq` are type correct.
-/

namespace Lean
namespace Meta

@[specialize] private def ensureType
    (whnf : Expr → MetaM Expr)
    (e : Expr) : MetaM Unit :=
do getLevelAux whnf (inferTypeAux whnf) e;
   pure ()

@[specialize] private def checkLambdaLet
    (whnf    : Expr → MetaM Expr)
    (isDefEq : Expr → Expr → MetaM Bool)
    (check   : Expr → MetaM Unit)
    (e : Expr) : MetaM Unit :=
lambdaTelescope whnf e $ fun xs b => do
  xs.forM $ fun x => do {
    xDecl ← getFVarLocalDecl x;
    match xDecl with
    | LocalDecl.cdecl _ _ _ t _ => do
      ensureType whnf t;
      check t
    | LocalDecl.ldecl _ _ _ t v => do
      ensureType whnf t;
      check t;
      vType ← inferTypeAux whnf v;
      unlessM (isDefEq t vType) $ throwEx $ Exception.letTypeMismatch x.fvarId!;
      check v
  };
  check b

@[specialize] private def checkForall
    (whnf    : Expr → MetaM Expr)
    (check   : Expr → MetaM Unit)
    (e : Expr) : MetaM Unit :=
forallTelescope whnf e $ fun xs b => do
  xs.forM $ fun x => do {
    xDecl ← getFVarLocalDecl x;
    ensureType whnf xDecl.type;
    check xDecl.type
  };
  ensureType whnf b;
  check b

@[specialize] private def checkConstant
    (c : Name) (lvls : List Level) : MetaM Unit :=
do env ← getEnv;
   match env.find c with
   | none       => throwEx $ Exception.unknownConst c
   | some cinfo => unless (lvls.length != cinfo.lparams.length) $ throwEx $ Exception.incorrectNumOfLevels c lvls

@[specialize] private def checkApp
    (whnf    : Expr → MetaM Expr)
    (isDefEq : Expr → Expr → MetaM Bool)
    (check   : Expr → MetaM Unit)
    (f a : Expr) : MetaM Unit :=
do check f;
   check a;
   fType ← inferTypeAux whnf f;
   fType ← whnf fType;
   match fType with
   | Expr.forallE _ d _ _ => do
     aType ← inferTypeAux whnf a;
     unlessM (isDefEq d aType) $ throwEx $ Exception.appTypeMismatch f a
   | _ => unless fType.isForall $ throwEx $ Exception.functionExpected fType #[a]

@[specialize] private partial def checkAuxAux
    (whnf    : Expr → MetaM Expr)
    (isDefEq : Expr → Expr → MetaM Bool)
    : Expr → MetaM Unit
| e@(Expr.forallE _ _ _ _) => checkForall whnf checkAuxAux e
| e@(Expr.lam _ _ _ _)     => checkLambdaLet whnf isDefEq checkAuxAux e
| e@(Expr.letE _ _ _ _ _)  => checkLambdaLet whnf isDefEq checkAuxAux e
| Expr.const c lvls _      => checkConstant c lvls
| Expr.app f a _           => checkApp whnf isDefEq checkAuxAux f a
| Expr.mdata _ e _         => checkAuxAux e
| Expr.proj _ _ e _        => checkAuxAux e
| _                        => pure ()

@[specialize] def checkAux
    (whnf    : Expr → MetaM Expr)
    (isDefEq : Expr → Expr → MetaM Bool)
    (e : Expr) : MetaM Unit :=
usingTransparency TransparencyMode.all $
  checkAuxAux whnf isDefEq e

@[specialize] def isTypeCorrectAux
    (whnf    : Expr → MetaM Expr)
    (isDefEq : Expr → Expr → MetaM Bool)
    (e : Expr) : MetaM Bool :=
catch
  (do checkAux whnf isDefEq e; pure true)
  (fun _ => pure false)

end Meta
end Lean
