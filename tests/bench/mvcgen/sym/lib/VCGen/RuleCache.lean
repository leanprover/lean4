/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public meta import Lean.Elab
public meta import Lean.Meta
public meta import Lean.Elab.Tactic.Do.VCGen.Split
public meta import VCGen.Context
public meta import VCGen.RuleConstruction
public meta import VCGen.Util

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

/-!
`VCGenM`-level cache wrappers around the `SymM` rule constructors in
`VCGen.RuleConstruction`. The cache key is `(declName, m, excessArgs.size)`.
-/

namespace VCGen

public meta def SpecTheoremNew.global? (specThm : SpecTheoremNew) : Option Name :=
  match specThm.proof with | .global decl => some decl | _ => none

/-- See the documentation for `mkBackwardRuleFromSpec` and `mkBackwardRuleFromSimpSpec`. -/
public meta def mkBackwardRuleFromSpecCached (specThm : SpecTheoremNew) (m σs ps instWP : Expr)
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
public meta def mkBackwardRuleFromSplitInfoCached (splitInfo : SplitInfo) (m σs ps instWP : Expr) (excessArgs : Array Expr) : _root_.VCGenM BackwardRule := do
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
