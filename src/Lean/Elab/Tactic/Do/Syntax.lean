/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Lean.Elab.BuiltinNotation
public import Std.Do.Triple.Basic

public section

namespace Std.Do

open Lean Parser Meta Elab Term PrettyPrinter Delaborator

open Std.Do in
@[builtin_delab PostCond.noThrow]
private def unexpandPostCondNoThrow : Delab := do
  match ← SubExpr.withAppArg <| delab with
  | `(fun $xs:term* => $e) =>
    let t ← `(⇓ $xs* => $(← SPred.Notation.unpack e))
    return ⟨t.raw⟩
  | t => `($(mkIdent ``PostCond.noThrow):term $t)

open Std.Do in
@[builtin_delab PostCond.mayThrow]
private def unexpandPostCondMayThrow : Delab := do
  match ← SubExpr.withAppArg <| delab with
  | `(fun $xs:term* => $e) =>
    let t ← `(⇓? $xs* => $(← SPred.Notation.unpack e))
    return ⟨t.raw⟩
  | t => `($(mkIdent ``PostCond.mayThrow):term $t)

@[inherit_doc Triple, builtin_doc, builtin_term_elab triple]
private def elabTriple : TermElab
  | `(⦃$P⦄ $x ⦃$Q⦄), _ => do
    -- In a simple world, this would just be a macro expanding to
    -- `Triple $x spred($P) spred($Q)`.
    -- However, currently we need to help type inference for P and Q.
    -- Specifically, if `x : StateT σ m α`, `[wp : WP m ps]` and `P : σ → Assertion ps`,
    -- then `Triple x P _` will not elaborate because `σ → Assertion ps =?= Assertion ?ps` fails.
    -- We must first instantiate `?ps` to `.arg σ ps` through the `outParam` of `WP`, hence this elaborator.
    -- This is tracked in #8766, and #8074 might be a fix.
    let (u, v, m, α, ps, inst, x) ← withRef x do
      let x ← elabTerm x none
      let ty ← inferType x
      tryPostponeIfMVar ty
      let ty ← instantiateMVars ty
      let .app m α := ty.consumeMData | throwError "Type of {x} is not a type application: {ty}"
      let some u ← Level.dec <$> getLevel α | throwError "Wrong level 0 {ty}"
      let some v ← Level.dec <$> getLevel ty | throwError "Wrong level 0 {ty}"
      let ps ← mkFreshExprMVar (mkConst ``PostShape [u])
      let inst ← synthInstance (mkApp2 (mkConst ``WP [u, v]) m ps)
      return (u, v, m, α, ps, inst, x)
    let P ← elabTerm (← `(spred($P))) (mkApp (mkConst ``Assertion [u]) ps)
    let Q ← elabTerm Q (mkApp2 (mkConst ``PostCond [u]) α ps)
    return mkApp7 (mkConst ``Triple [u, v]) m ps inst α x P Q
  | _, _ => throwUnsupportedSyntax
