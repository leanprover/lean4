/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.VCGen.Split
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction
public import Lean.Elab.Tactic.Do.Internal.VCGen.Util
import Lean.Meta.Sym.InferType

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.Internal.SpecAttr
open Lean.Elab.Tactic.Do.Internal

/-!
`VCGenM`-level cache wrappers around the `SymM` rule constructors in
`VCGen.RuleConstruction`.
-/

namespace Lean.Elab.Tactic.Do.Internal

namespace VCGen

/--
Cached version of spec rule construction.

Both `Triple`/`⊑ wp` and equality entries go through `tryMkBackwardRuleFromSpec`, which normalizes
an equality spec to `⊑ wp` form using the supplied `wp` metadata before building the rule.

Cache key: `(proof key, instWP, excessArgs.size)`.
-/
public def mkBackwardRuleFromSpecCached (specThm : SpecTheorem) (info : WPInfo) :
    OptionT VCGenM BackwardRule := do
  let key := (specThm.proof.key, ExprPtr.mk info.instWP, info.excessArgs.size)
  let s := (← get).specBackwardRuleCache
  if let some rule := s[key]? then return rule
  let some rule ← withNewMCtxDepth <| tryMkBackwardRuleFromSpec specThm info |>.run
    | failure
  let rule ← rule.shareCommon
  modify fun st => { st with specBackwardRuleCache := st.specBackwardRuleCache.insert key rule }
  return rule

open Lean.Elab.Tactic.Do in
/--
Cached version of `mkBackwardRuleForSplit`.

Cache key: `(splitter name, instWP, excessArgs.size)`.
-/
public def mkBackwardRuleForSplitCached (splitInfo : SplitInfo) (info : WPInfo) :
    VCGenM BackwardRule := do
  let cacheKey := match splitInfo with
    | .ite .. => ``ite
    | .dite .. => ``dite
    | .matcher matcherApp => matcherApp.matcherName
  let key := (cacheKey, ExprPtr.mk info.instWP, info.excessArgs.size)
  let s := (← get).splitBackwardRuleCache
  if let some rule := s[key]? then return rule
  let rule ← mkBackwardRuleForSplit splitInfo info
  let rule ← rule.shareCommon
  modify fun st =>
    { st with splitBackwardRuleCache := st.splitBackwardRuleCache.insert key rule }
  return rule

/--
Cached version of `LatticeSplit.mkBackwardRuleForLattice`.

Cache key: `(split lemma, argument types, excessArgs.size)`.
-/
public def mkBackwardRuleForLatticeCached (c : LatticeSplit) (params as excessArgs : Array Expr)
    (resultType? : Option Expr := none) : VCGenM BackwardRule := do
  let s := (← get).latticeBackwardRuleCache
  let asTypes ← (as.mapM Sym.inferType : SymM (Array Expr))
  -- `params` (e.g. the frame operator of `PreservesSup.upperAdjoint`) is functionally determined by `asTypes`,
  -- so it need not enter the cache key.
  let key := (c.relLemma, asTypes.map ExprPtr.mk, excessArgs.size)
  if let some rule := s[key]? then return rule
  let rule ← c.mkBackwardRuleForLattice params as excessArgs resultType?
  let rule ← rule.shareCommon
  modify fun st => { st with latticeBackwardRuleCache := st.latticeBackwardRuleCache.insert key rule }
  return rule

/-- The backward rule for a direct split (`applyLemma := none`): `relLemma` applied as-is, with its
premises becoming subgoals. Cached in `latticeBackwardRuleCache` keyed by `relLemma`. -/
public def mkBackwardRuleForLatticeDirectCached (c : LatticeSplit) : VCGenM BackwardRule := do
  let key := (c.relLemma, (#[] : Array ExprPtr), 0)
  let s := (← get).latticeBackwardRuleCache
  if let some rule := s[key]? then return rule
  let rule ← Sym.mkBackwardRuleFromDecl c.relLemma
  let rule ← rule.shareCommon
  modify fun st => { st with latticeBackwardRuleCache := st.latticeBackwardRuleCache.insert key rule }
  return rule

end VCGen

end Lean.Elab.Tactic.Do.Internal
