/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic
import Init.Lean.Meta.FunInfo

namespace Lean
namespace Meta

partial def reduceAux (explicitOnly : Bool) (skipTypes : Bool) (skipProofs : Bool) : Expr → MetaM Expr
| e => do
  condM (pure skipTypes <&&> isType e) (pure e) $
  condM (pure skipProofs <&&> isProof e) (pure e) $ do
    e ← whnf e;
    match e with
    | Expr.app _ _ _       => do
      let f     := e.getAppFn;
      let nargs := e.getAppNumArgs;
      finfo ← getFunInfoNArgs f nargs;
      let args  := e.getAppArgs;
      args ← args.size.foldM
        (fun i (args : Array Expr) =>
          if h : i < finfo.paramInfo.size then
            let info := finfo.paramInfo.get ⟨i, h⟩;
            if explicitOnly && (info.implicit || info.instImplicit) then
              pure args
            else
              args.modifyM i reduceAux
          else
            args.modifyM i reduceAux)
        args;
      pure $ mkAppN f args
    | Expr.lam _ _ _ _     => lambdaTelescope e $ fun xs b => do b ← reduceAux b; mkLambda xs b
    | Expr.forallE _ _ _ _ => forallTelescope e $ fun xs b => do b ← reduceAux b; mkForall xs b
    | _ => pure e

def reduce (e : Expr) (explicitOnly skipTypes skipProofs := true) : MetaM Expr :=
reduceAux explicitOnly skipTypes skipProofs e

end Meta
end Lean
