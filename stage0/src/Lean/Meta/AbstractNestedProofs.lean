/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Closure

namespace Lean
namespace Meta
namespace AbstractNestedProofs

def isNonTrivialProof (e : Expr) : MetaM Bool :=
condM (not <$> isProof e) (pure false) $ e.withApp fun f args =>
  pure $ !f.isAtomic || args.any fun arg => !arg.isAtomic

structure Context :=
(baseName : Name)

structure State :=
(nextIdx : Nat := 1)

abbrev M := ReaderT Context $ MonadCacheT Expr Expr $ StateRefT State $ MetaM

private def mkAuxLemma (e : Expr) : M Expr := do
ctx ← read;
s ← get;
lemmaName ← mkAuxName (ctx.baseName ++ `proof) s.nextIdx;
modify fun s => { s with nextIdx := s.nextIdx + 1 };
mkAuxDefinitionFor lemmaName e

partial def visit : Expr → M Expr
| e =>
  if e.isAtomic then pure e
  else do
    let visitBinders (xs : Array Expr) (k : M Expr) : M Expr := do {
      localInstances ← getLocalInstances;
      lctx ← getLCtx;
      lctx ← xs.foldlM
        (fun (lctx : LocalContext) x => do
          let xFVarId := x.fvarId!;
          localDecl ← getLocalDecl xFVarId;
          type      ← visit localDecl.type;
          let localDecl := localDecl.setType type;
          localDecl ← match localDecl.value? with
            | some value => do value ← visit value; pure $ localDecl.setValue value
            | none       => pure localDecl;
          pure $ lctx.modifyLocalDecl xFVarId fun _ => localDecl)
        lctx;
      withLCtx lctx localInstances k
    };
    checkCache e fun e => condM (liftM $ isNonTrivialProof e) (mkAuxLemma e) $ match e with
    | Expr.lam _ _ _ _     => lambdaLetTelescope e fun xs b => visitBinders xs do b ← visit b; mkLambdaFVars xs b
    | Expr.letE _ _ _ _ _  => lambdaLetTelescope e fun xs b => visitBinders xs do b ← visit b; mkLambdaFVars xs b
    | Expr.forallE _ _ _ _ => forallTelescope e fun xs b => visitBinders xs do b ← visit b; mkForallFVars xs b
    | Expr.mdata _ b _     => do b ← visit b; pure $ e.updateMData! b
    | Expr.proj _ _ b _    => do b ← visit b; pure $ e.updateProj! b
    | Expr.app _ _ _       => e.withApp fun f args => do args ← args.mapM visit; pure $ mkAppN f args
    | _                    => pure e

end AbstractNestedProofs

/-- Replace proofs nested in `e` with new lemmas. The new lemmas have names of the form `mainDeclName.proof_<idx>` -/
def abstractNestedProofs (mainDeclName : Name) (e : Expr) : MetaM Expr :=
(((AbstractNestedProofs.visit e).run { baseName := mainDeclName }).run).run' { nextIdx := 1 }

end Meta
end Lean
