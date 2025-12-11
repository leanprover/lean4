/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Grind.Util
public import Lean.Meta.Closure
public import Lean.Meta.Transform

public section

namespace Lean.Meta

/-- Abstracts the given proof into an auxiliary theorem, suitably pre-processing its type. -/
def abstractProof [Monad m] [MonadLiftT MetaM m] [MonadEnv m] [MonadOptions m] [MonadFinally m]
    (proof : Expr) (cache := true) (postprocessType : Expr → m Expr := pure) : m Expr := do
  let type ← withoutExporting do inferType proof
  let type ← (Core.betaReduce type : MetaM _)
  let type ← zetaReduce type
  let type ← postprocessType type
  /- https://github.com/leanprover/lean4/issues/10196
     If we use the cache when the proof contains `sorry`,
     then we may fail to get a "declaration uses `sorry`" warning for the current declaration. -/
  let cache := cache && !proof.hasSorry
  /- We turn on zetaDelta-expansion to make sure we don't need to perform an expensive `check` step to
    identify which let-decls can be abstracted. If we design a more efficient test, we can avoid the eager zetaDelta expansion step.
    In a benchmark created by @selsam, The extra `check` step was a bottleneck. -/
  mkAuxTheorem (cache := cache) type proof (zetaDelta := true)

namespace AbstractNestedProofs

def getLambdaBody (e : Expr) : Expr :=
  match e with
  | .lam _ _ b _ => getLambdaBody b
  | _ => e

def isNonTrivialProof (e : Expr) : MetaM Bool := do
  let origEnv ← getEnv
  -- NOTE: this `withoutExporting` is not strictly necessary when considering the Lean elaborator
  -- per se because there `e` is an elaboration result that should have been produced under the same
  -- `Environment.isExporting` setting as the current one, so all referenced constants should be
  -- accessible as is. However, Mathlib's `[to_additive]`, for example, uses `abstractNestedProofs`
  -- on terms that contain the unfolding of non-exposed definitions and so may reference private
  -- declarations but the code might still be run under `isExporting = true` in order to create the
  -- new aux decls in the public scope. Thus we always shift to the private scope here.
  withoutExporting do
  if !(← isProof e) then
    return false
  else if e.isAppOf ``Grind.nestedProof then
    -- Grind.nestedProof is a gadget created by the `grind` tactic.
    -- We want to avoid the situation where `grind` keeps creating them,
    -- and this module, which is used by `grind`, keeps abstracting them.
    return false
  else
    -- We consider proofs such as `fun x => f x a` as trivial.
    -- For example, we don't want to abstract the body of `def rfl`
    (getLambdaBody e).withApp fun f args =>
      pure $ !f.isAtomic ||
        -- Again we may need to re-do an abstraction here for `to_additive` even if in base
        -- elaborator, this condition should never be fulfilled
        f.const?.any (!origEnv.contains ·.1) ||
        args.any fun arg => !arg.isAtomic

structure Context where
  cache    : Bool

abbrev M := ReaderT Context $ MonadCacheT ExprStructEq Expr MetaM

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
        let localDecl ← match localDecl.value? (allowNondep := true) with
           | some value => let value ← visit value; pure <| localDecl.setValue value
           | none       => pure localDecl
        lctx := lctx.modifyLocalDecl xFVarId fun _ => localDecl
      withLCtx lctx localInstances k
    checkCache { val := e : ExprStructEq } fun _ => do
      if (← isNonTrivialProof e) then
        /- Ensure proofs nested in type are also abstracted -/
        abstractProof e (← read).cache visit
      else match e with
        | .lam ..
        | .letE ..     => lambdaLetTelescope e fun xs b => visitBinders xs do mkLambdaFVars xs (← visit b) (usedLetOnly := false) (generalizeNondepLet := false)
        | .forallE ..  => forallTelescope e fun xs b => visitBinders xs do mkForallFVars xs (← visit b)
        | .mdata _ b   => return e.updateMData! (← visit b)
        | .proj _ _ b  => return e.updateProj! (← visit b)
        | .app ..      => e.withApp fun f args => return mkAppN (← visit f) (← args.mapM visit)
        | _            => pure e

end AbstractNestedProofs

/-- Replace proofs nested in `e` with new lemmas. The new lemmas are named using `getDeclNGen`. -/
def abstractNestedProofs (e : Expr) (cache := true) : MetaM Expr := do
  if (← isProof e) then
    -- `e` is a proof itself. So, we don't abstract nested proofs
    return e
  else
    AbstractNestedProofs.visit e |>.run { cache } |>.run

end Lean.Meta
