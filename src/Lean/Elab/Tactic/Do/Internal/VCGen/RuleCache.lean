/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.VCGen.Split
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction
public import Lean.Elab.Tactic.Do.Internal.VCGen.Util

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Lean.Elab.Tactic.Do.Internal
open Std.Do

/-!
`VCGenM`-level cache wrappers around the `SymM` rule constructors in
`VCGen.RuleConstruction`. The cache key is `(declName, m, excessArgs.size)`.
-/

namespace Lean.Elab.Tactic.Do.Internal

set_option linter.checkUnivs false in
@[inline]
def Std.HashMap.getDM [Monad m] [BEq α] [Hashable α]
    (cache : Std.HashMap α β) (key : α) (fallback : m β) : m (β × Std.HashMap α β) := do
  if let some b := cache.get? key then
    return (b, cache)
  let b ← fallback
  return (b, cache.insert key b)

namespace VCGen

public def SpecTheoremNew.global? (specThm : SpecTheoremNew) : Option Name :=
  match specThm.proof with | .global decl => some decl | _ => none

/-- See the documentation for `mkBackwardRuleFromSpec` and `mkBackwardRuleFromSimpSpec`. -/
public def mkBackwardRuleFromSpecCached (specThm : SpecTheoremNew) (m σs ps instWP : Expr)
    (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let mkRuleSlow := match specThm.kind with
    | .triple _ => mkBackwardRuleFromSpec     specThm m σs ps instWP excessArgs
    | .simp _   => mkBackwardRuleFromSimpSpec specThm m σs ps instWP excessArgs
  let s ← get
  let some decl := SpecTheoremNew.global? specThm | mkRuleSlow
  let (res, specBackwardRuleCache) ← s.specBackwardRuleCache.getDM (decl, m, excessArgs.size) mkRuleSlow
  set { s with specBackwardRuleCache }
  return res

open Lean.Elab.Tactic.Do in
/-- Creates and caches a backward rule for splitting `ite`, `dite`, or matchers. -/
public def mkBackwardRuleFromSplitInfoCached (splitInfo : SplitInfo) (m σs ps instWP : Expr) (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let cacheKey := match splitInfo with
    | .ite .. => ``ite
    | .dite .. => ``dite
    | .matcher matcherApp => matcherApp.matcherName
  let mkRuleSlow := mkBackwardRuleForSplit splitInfo m σs ps instWP excessArgs
  let s ← get
  let (res, splitBackwardRuleCache) ← s.splitBackwardRuleCache.getDM (cacheKey, m, excessArgs.size) mkRuleSlow
  set { s with splitBackwardRuleCache }
  return res

end VCGen

end Lean.Elab.Tactic.Do.Internal
