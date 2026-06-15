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
Cached version of ordinary and equality spec rule construction.

Ordinary `Triple`/`⊑ wp` entries are sent to `tryMkBackwardRuleFromSpec`; equality entries are sent
to `tryMkBackwardRuleFromSimp`. The caller supplies the full `wp` metadata because equality
specs must check that their equation type is definitionally equal to `m α`.

Cache key: `(proof key, instWP, excessArgs.size)`.
-/
public def mkBackwardRuleFromSpecCached (specThm : SpecTheorem) (info : WPInfo) :
    OptionT VCGenM BackwardRule := do
  let key := (specThm.proof.key, info.instWP, info.excessArgs.size)
  let s := (← get).specBackwardRuleCache
  if let some rule := s[key]? then return rule
  let some rule ← withNewMCtxDepth <| match specThm.kind with
      | .triple => tryMkBackwardRuleFromSpec specThm info |>.run
      | .simp _ => tryMkBackwardRuleFromSimp specThm info |>.run
    | failure
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
  let key := (cacheKey, info.instWP, info.excessArgs.size)
  let s := (← get).splitBackwardRuleCache
  if let some rule := s[key]? then return rule
  let rule ← mkBackwardRuleForSplit splitInfo info
  modify fun st =>
    { st with splitBackwardRuleCache := st.splitBackwardRuleCache.insert key rule }
  return rule

/--
Cached version of `LogicOp.mkBackwardRule`.

Cache key: `(logic rule lemma, argument types, excessArgs.size, preIsTop)`. The `preIsTop` flag is
part of the key because a `⊤` precondition produces a `⊤`-specialized rule whose type differs from
the general one.
-/
public def mkBackwardRuleForLogicCached (lop : LogicOp) (as excessArgs : Array Expr)
    (resultType? : Option Expr := none) (preIsTop : Bool := false) : VCGenM BackwardRule := do
  let s := (← get).logicBackwardRuleCache
  let asTypes ← (as.mapM Sym.inferType : SymM (Array Expr))
  let key := (lop.toApplyLemma, asTypes, excessArgs.size, preIsTop)
  if let some rule := s[key]? then return rule
  let rule ← LogicOp.mkBackwardRule lop as excessArgs resultType? preIsTop
  modify fun st => { st with logicBackwardRuleCache := st.logicBackwardRuleCache.insert key rule }
  return rule

end VCGen

end Lean.Elab.Tactic.Do.Internal
