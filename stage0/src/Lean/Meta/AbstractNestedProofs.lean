/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Closure

namespace Lean.Meta
namespace AbstractNestedProofs

def isNonTrivialProof (e : Expr) : MetaM Bool := do
  if !(← isProof e) then
    pure false
  else
    e.withApp fun f args =>
      pure $ !f.isAtomic || args.any fun arg => !arg.isAtomic

structure Context where
  baseName : Name

structure State where
  nextIdx : Nat := 1

abbrev M := ReaderT Context $ MonadCacheT ExprStructEq Expr $ StateRefT State MetaM

private def mkAuxLemma (e : Expr) : M Expr := do
  let ctx ← read
  let s ← get
  let lemmaName ← mkAuxName (ctx.baseName ++ `proof) s.nextIdx
  modify fun s => { s with nextIdx := s.nextIdx + 1 }
  /- We turn on zeta-expansion to make sure we don't need to perform an expensive `check` step to
     identify which let-decls can be abstracted. If we design a more efficient test, we can avoid the eager zeta expasion step.
     It a benchmark created by @selsam, The extra `check` step was a bottleneck. -/
  mkAuxDefinitionFor lemmaName e (zeta := true)

partial def visit (e : Expr) : M Expr := do
  if e.isAtomic then
    pure e
  else
    let visitBinders (xs : Array Expr) (k : M Expr) : M Expr := do
      let localInstances ← getLocalInstances
      let mut lctx ← getLCtx
      for x in xs do
        let xFVarId := x.fvarId!
        let localDecl ← getLocalDecl xFVarId
        let type      ← visit localDecl.type
        let localDecl := localDecl.setType type
        let localDecl ← match localDecl.value? with
           | some value => do let value ← visit value; pure $ localDecl.setValue value
           | none       => pure localDecl
        lctx :=lctx.modifyLocalDecl xFVarId fun _ => localDecl
      withLCtx lctx localInstances k
    checkCache { val := e : ExprStructEq } fun _ => do
      if (← isNonTrivialProof e) then
        mkAuxLemma e
      else match e with
        | Expr.lam _ _ _ _     => lambdaLetTelescope e fun xs b => visitBinders xs do mkLambdaFVars xs (← visit b)
        | Expr.letE _ _ _ _ _  => lambdaLetTelescope e fun xs b => visitBinders xs do mkLambdaFVars xs (← visit b)
        | Expr.forallE _ _ _ _ => forallTelescope e fun xs b => visitBinders xs do mkForallFVars xs (← visit b)
        | Expr.mdata _ b _     => return e.updateMData! (← visit b)
        | Expr.proj _ _ b _    => return e.updateProj! (← visit b)
        | Expr.app _ _ _       => e.withApp fun f args => return mkAppN f (← args.mapM visit)
        | _                    => pure e

end AbstractNestedProofs

/-- Replace proofs nested in `e` with new lemmas. The new lemmas have names of the form `mainDeclName.proof_<idx>` -/
def abstractNestedProofs (mainDeclName : Name) (e : Expr) : MetaM Expr :=
  AbstractNestedProofs.visit e |>.run { baseName := mainDeclName } |>.run |>.run' { nextIdx := 1 }

end Lean.Meta
