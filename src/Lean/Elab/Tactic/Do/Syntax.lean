/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Init.NotationExtra
import Lean.Elab.BuiltinNotation
import Std.Do.PostCond
import Std.Do.Triple.Basic

namespace Std.Do

open Lean Parser Meta Elab Term PrettyPrinter Delaborator

open Std.Do in
@[builtin_delab app.Std.Do.PostCond.total]
private meta def unexpandPostCondTotal : Delab := do
  match ← SubExpr.withAppArg <| delab with
  | `(fun $xs:term* => $e) =>
    let t ← `(⇓ $xs* => $(← SPred.Notation.unpack e))
    return ⟨t.raw⟩
  | t => `($(mkIdent ``PostCond.total):term $t)

@[inherit_doc Triple, builtin_doc, builtin_term_elab triple]
private meta def elabTriple : TermElab
  | `(⦃$P⦄ $x ⦃$Q⦄), _ => do
    -- In a simple world, this would just be a macro expanding to
    -- `Triple $x spred($P) spred($Q)`.
    -- However, currently we need to help type inference for P and Q.
    -- Specifically, if `x : StateT σ m α`, `[wp : WP m ps]` and `P : σ → Assertion ps`,
    -- then `Triple x P _` will not elaborate because `σ → Assertion ps =?= Assertion ?ps` fails.
    -- We must first instantiate `?ps` to `.arg σ ps` through the `outParam` of `WP`, hence this elaborator.
    -- This is tracked in #8766, and #8074 might be a fix.
    let (u, m, α, ps, inst, x) ← withRef x do
      let x ← elabTerm x none
      let ty ← inferType x
      tryPostponeIfMVar ty
      let ty ← instantiateMVars ty
      let .app m α := ty.consumeMData | throwError "Type of {x} is not a type application: {ty}"
      let some u ← Level.dec <$> getLevel ty | throwError "Wrong level 0 {ty}"
      let ps ← mkFreshExprMVar (mkConst ``PostShape)
      let inst ← synthInstance (mkApp2 (mkConst ``WP [u]) m ps)
      return (u, m, α, ps, inst, x)
    let P ← elabTerm (← `(spred($P))) (mkApp (mkConst ``Assertion) ps)
    let Q ← elabTerm (← `(spred($Q))) (mkApp2 (mkConst ``PostCond) α ps)
    return mkApp7 (mkConst ``Triple [u]) m ps inst α x P Q
  | _, _ => throwUnsupportedSyntax
