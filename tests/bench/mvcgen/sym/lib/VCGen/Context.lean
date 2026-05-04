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
meta import Lean.Meta.Sym.Pattern
meta import Lean.Meta.Sym.Simp.DiscrTree
public meta import Lean.Meta.Tactic.Grind.Main
public meta import Lean.Elab.Tactic.Do.VCGen.Basic
public meta import VCGen.SpecDB

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

/-!
The `VCGenM` monad: its read-only `Context` (spec database + a fixed bundle of
pre-built `BackwardRule`s + user-customisable simp methods + pre-tactic) and
its mutable `State` (rule caches, accumulated invariants/VCs, simp cache).
-/

/-- Pre-tactic to try on each emitted VC before returning it to the user. -/
public inductive VCGen.PreTac where
  /-- No pre-tactic; VCs are returned as-is. -/
  | none
  /-- Use grind with the given hypothesis simplification methods. -/
  | grind
  /-- Use a user-provided tactic syntax. -/
  | tactic (tac : Syntax)

public meta def VCGen.PreTac.isGrind : VCGen.PreTac → Bool
  | .grind => true
  | _ => false

public structure VCGen.Context where
  specThms : SpecTheoremsNew
  /-- The backward rule for `SPred.entails_cons_intro`. -/
  entailsConsIntroRule : BackwardRule
  /-- The backward rule for `SPred.entails_nil_pure_intro`. Preferred over `entails_nil_intro`
  when the LHS is `⌜φ⌝`, as it unwraps `.down` on the pure assertion. -/
  entailsNilPureIntroRule : BackwardRule
  /-- The backward rule for `SPred.entails_nil_intro`. Fallback when LHS is not `⌜φ⌝`. -/
  entailsNilIntroRule : BackwardRule
  /-- The backward rule for `SPred.apply_pure_cons_entails_l`. Peels a state arg from
  `SPred.pure (σ::σs) φ s` on the LHS of an entailment. -/
  applyPureConsEntailsLRule : BackwardRule
  /-- The backward rule for `SPred.apply_pure_cons_entails_r`. Peels a state arg from
  `SPred.pure (σ::σs) φ s` on the RHS of an entailment. -/
  applyPureConsEntailsRRule : BackwardRule
  /-- The backward rule for `SPred.down_pure_intro`. Reduces a target of the form
  `(SPred.pure [] φ).down` to `φ`. -/
  downPureIntroRule : BackwardRule
  /-- The backward rule for `SPred.pure_elim'`. -/
  pureElimRule : BackwardRule
  /-- The backward rule for `SPred.pure_intro`. -/
  pureIntroRule : BackwardRule
  /-- The backward rule for `PostCond.entails.rfl`. Tried first to close by reflexivity. -/
  postCondEntailsRflRule : BackwardRule
  /-- The backward rule for `PostCond.entails.mk`. -/
  postCondEntailsMkRule : BackwardRule
  /-- The backward rule for `ExceptConds.entails.rfl`. -/
  exceptCondsEntailsRflRule : BackwardRule
  /-- The backward rule for `ExceptConds.entails.pure`. Closes the exception side for
  pure PostShapes, where `ExceptConds.entails` reduces to `True`. -/
  exceptCondsEntailsPureRule : BackwardRule
  /-- The backward rule for `ExceptConds.entails_false`. -/
  exceptCondsEntailsFalseRule : BackwardRule
  /-- The backward rule for `ExceptConds.entails_true`. -/
  exceptCondsEntailsTrueRule : BackwardRule
  /-- The backward rule for `Triple.of_entails_wp`. -/
  tripleOfEntailsWPRule : BackwardRule
  /-- The backward rule for `And.intro`. -/
  andIntroRule : BackwardRule
  /-- User-customizable simp methods used to pre-simplify hypotheses. -/
  hypSimpMethods : Option Sym.Simp.Methods := none
  /-- Pre-tactic to try on each emitted VC. -/
  preTac : PreTac := .none
  /-- If `true`, treat `__do_jp` bindings as shared continuations (linear in the number of
  control-flow splits) instead of zeta-unfolding them at every call site (the default;
  exponential blow-up on nested splits). Maps to the `jp` config option. -/
  useJP : Bool := false

public structure VCGen.State where
  /--
  A cache mapping registered SpecThms to their backward rule to apply.
  The particular rule depends on the theorem name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  specBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /--
  A cache mapping matchers to their splitting backward rule to apply.
  The particular rule depends on the matcher name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  splitBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /--
  Holes of type `Invariant` that have been generated so far.
  -/
  invariants : Array MVarId := #[]
  /--
  The verification conditions that have been generated so far.
  -/
  vcs : Array MVarId := #[]
  /--
  Persistent cache for the `Sym.Simp` simplifier used to pre-simplify hypotheses
  before grind internalization. Threading this cache across VCGen iterations avoids
  re-simplifying shared subexpressions (e.g., `s + 1 + 1 + ...` chains).
  -/
  simpState : Sym.Simp.State := {}
  /--
  Map from `__do_jp` fvar id to its `JumpSiteInfo`. Populated when `tryLetIntro`
  registers a join point (`Context.useJP = true`); consulted by `tryFvarZeta` /
  `tryJumpSite` to short-circuit zeta-unfolding at call sites.
  -/
  jps : FVarIdMap JumpSiteInfo := {}

public abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State Grind.GrindM)

namespace VCGen

/-- Register a join-point `JumpSiteInfo` for the given fvar. Called when a
`let __do_jp := …` is detected as a shared continuation. -/
public meta def registerJP (fv : FVarId) (info : JumpSiteInfo) : _root_.VCGenM Unit :=
  modify fun s => { s with jps := s.jps.insert fv info }

/-- Look up a previously-registered join point by fvar id. -/
public meta def knownJP? (fv : FVarId) : _root_.VCGenM (Option JumpSiteInfo) :=
  return (← get).jps.get? fv

end VCGen
