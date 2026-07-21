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
public import Lean.Elab.Tactic.Do.Internal.VCGen.LatticeOp
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
public def mkBackwardRuleFromSpecCached (specThm : SpecTheorem) (info : WPApp) :
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
public def mkBackwardRuleForSplitCached (splitInfo : SplitInfo) (info : WPApp) :
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
Cached construction of a lattice-split backward rule for the operator heading `rhs`. On a cache miss
the rewrite and terminal sets are assembled from the built-in seeds and the operator's `@[frameproc]`
contributions (`fp?`); a cache hit skips that work.

Cache key: the `head … cₙ` prefix built from the constant arguments (which the rule bakes in verbatim)
and the argument count (which fixes the schematic operand and state count).
-/
public def mkLatticeOpRuleCached (rhs : Expr) (op : LatticeOp) :
    VCGenM BackwardRule := do
  let key := (ExprPtr.mk (rhs.getAppPrefix op.numConst), rhs.getAppNumArgs)
  if let some rule := (← get).latticeBackwardRuleCache[key]? then return rule
  let rule ← (← mkLatticeOpRule rhs op).shareCommon
  modify fun st => { st with latticeBackwardRuleCache := st.latticeBackwardRuleCache.insert key rule }
  return rule

/--
Cached version of `mkFrameBackwardRule`.

Cache key: `(instWP, excessArgs.size)` (the operator is determined by the monad).
-/
public def mkFrameBackwardRuleCached (op : Expr) (info : WPApp) : VCGenM BackwardRule := do
  let key := (ExprPtr.mk info.instWP, info.excessArgs.size)
  if let some rule := (← get).frameBackwardRuleCache[key]? then return rule
  let rule ← (← mkFrameBackwardRule op info).shareCommon
  modify fun st => { st with frameBackwardRuleCache := st.frameBackwardRuleCache.insert key rule }
  return rule

end VCGen

end Lean.Elab.Tactic.Do.Internal
