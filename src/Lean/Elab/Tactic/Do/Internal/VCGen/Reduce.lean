/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.WHNF
import Lean.Meta.Sym

open Lean Meta Sym

namespace Lean.Elab.Tactic.Do.Internal

namespace VCGen

/-!
SymM-level head-redex reducer used throughout VCGen.
-/

/--
Repeatedly reduces head redexes in `e`, cycling through the following reductions until
no further progress is made:

1. **Beta**: `(fun x₁ ... xₘ => b) a₁ ... aₙ` → `b[a₁/x₁, aₘ/xₘ] aₘ₊₁ ... aₙ`
2. **Iota**: `MyType.casesOn (MyType.ctor args) alts` → `altᵢ args`
   (matcher/recursor applied to a constructor, at reducible transparency)
3. **Proj-reduction**: `⟨a, b, c⟩.1` → `a` (kernel `.proj` nodes)
4. **Projection delta**: `Struct.field x` → `x.5` (unfolds projection *functions*,
   progress only if followed by proj-reduction)

Returns `none` when no reduction was possible. Maintains maximal sharing via `shareCommonInc`.
-/
public partial def reduceHead? (e : Expr) : SymM (Option Expr) :=
  withReducible <| go none e.getAppFn e.getAppRevArgs
  where
    go lastReduction f rargs := do
      match f with
      | .mdata _ f => go lastReduction f rargs
      | .app f a => go lastReduction f (rargs.push a)
      | .lam .. =>
        if rargs.size = 0 then return lastReduction
        let e' := f.betaRev rargs
        let e' ← Sym.shareCommonInc e'
        go (some e') e'.getAppFn e'.getAppRevArgs
      | .const name .. =>
        -- projections
        if ← isProjectionFn name then
          let some e' ← Meta.unfoldDefinition? (mkAppRev f rargs) | return lastReduction
          let e' ← Sym.unfoldReducible e'
          let e' ← Sym.shareCommonInc e'
          go lastReduction e'.getAppFn e'.getAppRevArgs  -- intentional lastReduction! see docstring
        -- iota reduction: match/recursor with concrete discriminant
        else if let some e' ← liftMetaM <| reduceRecMatcher? (mkAppRev f rargs) then
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
        else
          pure lastReduction
      | .proj .. =>
        -- whnf at `instances` transparency: unfold `instMyAddInt32` (an instance) to
        -- expose its `MyAdd.mk` constructor so `reduceProj?` can project the field,
        -- but do not unfold arbitrary user definitions.
        match ← withReducibleAndInstances (reduceProj? f) with
        | some f' =>
          let f' ← Sym.unfoldReducible f'
          let f' ← Sym.shareCommonInc f'
          let e' := mkAppRev f' rargs
          go (some e') e'.getAppFn e'.getAppRevArgs
        | none    => pure lastReduction
      | _ => pure lastReduction

public def reduceHead (e : Expr) : SymM Expr :=
  return (← reduceHead? e).getD e

end VCGen
end Lean.Elab.Tactic.Do.Internal
