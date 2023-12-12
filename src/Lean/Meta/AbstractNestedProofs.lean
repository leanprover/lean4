/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Closure

namespace Lean.Meta
namespace AbstractNestedProofs

def getLambdaBody (e : Expr) : Expr :=
  match e with
  | .lam _ _ b _ => getLambdaBody b
  | _ => e

def isNonTrivialProof (e : Expr) : MetaM Bool := do
  if !(← isProof e) then
    pure false
  else
    -- We consider proofs such as `fun x => f x a` as trivial.
    -- For example, we don't want to abstract the body of `def rfl`
    (getLambdaBody e).withApp fun f args =>
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
     identify which let-decls can be abstracted. If we design a more efficient test, we can avoid the eager zeta expansion step.
     It a benchmark created by @selsam, The extra `check` step was a bottleneck. -/
  mkAuxTheoremFor lemmaName e (zeta := true)

partial def visit (e : Expr) : M Expr := do
  if e.isAtomic then
    pure e
  else
    let visitBinders (xs : Array Expr) (k : M Expr) : M Expr := do
      let localInstances ← getLocalInstances
      let mut lctx ← getLCtx
      for x in xs do
        let xFVarId := x.fvarId!
        let localDecl ← xFVarId.getDecl
        let type      ← visit localDecl.type
        let localDecl := localDecl.setType type
        let localDecl ← match localDecl.value? with
           | some value => let value ← visit value; pure <| localDecl.setValue value
           | none       => pure localDecl
        lctx :=lctx.modifyLocalDecl xFVarId fun _ => localDecl
      withLCtx lctx localInstances k
    checkCache { val := e : ExprStructEq } fun _ => do
      if (← isNonTrivialProof e) then
        mkAuxLemma e
      else match e with
        | .lam ..      => lambdaLetTelescope e fun xs b => visitBinders xs do mkLambdaFVars xs (← visit b) (usedLetOnly := false)
        | .letE ..     => lambdaLetTelescope e fun xs b => visitBinders xs do mkLambdaFVars xs (← visit b) (usedLetOnly := false)
        | .forallE ..  => forallTelescope e fun xs b => visitBinders xs do mkForallFVars xs (← visit b)
        | .mdata _ b   => return e.updateMData! (← visit b)
        | .proj _ _ b  => return e.updateProj! (← visit b)
        | .app ..      => e.withApp fun f args => return mkAppN f (← args.mapM visit)
        | _            => pure e

end AbstractNestedProofs

/-- Replace proofs nested in `e` with new lemmas. The new lemmas have names of the form `mainDeclName.proof_<idx>` -/
def abstractNestedProofs (mainDeclName : Name) (e : Expr) : MetaM Expr := do
  if (← isProof e) then
    -- `e` is a proof itself. So, we don't abstract nested proofs
    return e
  else
    AbstractNestedProofs.visit e |>.run { baseName := mainDeclName } |>.run |>.run' { nextIdx := 1 }

end Lean.Meta
