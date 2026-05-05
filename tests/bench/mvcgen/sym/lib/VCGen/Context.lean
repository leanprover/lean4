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
  /-- The `trivial` config option: when `true` (default), `Driver.emitVC` runs
  `repeatAndRfl` to collapse trivial `And.intro` chains; when `false`, the goal is
  emitted as-is. -/
  trivial : Bool := true
  /-- The `jp` config option: when `true`, `tryLetIntro` recognises `__do_jp` lets
  whose body is a splitter and sets up shared-continuation handling instead of
  zeta-unfolding. When `false` (default, matching original `mvcgen`), every call
  site of the JP zeta-unfolds, leading to exponential blow-up on nested splits. -/
  useJP : Bool := false
  /-- The `errorOnMissingSpec` config option: when `true` (default), `Driver.work`
  raises a hard error when `solve` returns `.noSpecFoundForProgram`. When `false`,
  the goal is emitted as an unsolved VC for the user to discharge — useful with
  `mvcgen' [-some_spec]` patterns where the user knows the spec is intentionally
  removed and wants to handle the residual goal by hand. -/
  errorOnMissingSpec : Bool := true
  /-- Pre-parsed `invariants`/`invariants?` alternatives, indexed by 1-based invariant
  number. Bullet form maps positions to entries (`bullet n+1 → alt`); labelled form maps
  the parsed `inv<n>` numbers (out-of-order labels are supported). Empty when no
  `invariants` clause is provided or in `invariants?` (suggest) mode (handled separately). -/
  invariantAlts : Std.HashMap Nat Syntax := {}

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
  /--
  Remaining VC-generation steps. Initialized from `Context.config.stepLimit` (or
  `.unlimited` when no limit is set). Decremented at each successful program-shape
  step (`tryLetHoist`, `trySplit`, `tryFvarZeta`, `applySpec`). When exhausted,
  `solve` short-circuits and emits the current goal as a VC.
  -/
  fuel : Lean.Elab.Tactic.Do.Fuel := .unlimited
  /--
  Set of invariant numbers that have been inline-elaborated by `Driver.emitVC` via
  `tryInlineInvariant`. The post-hoc invariant elaboration in `Frontend` consults
  this to know which user-provided alts have already been consumed (so it doesn't
  warn about them). -/
  inlineHandledInvariants : Std.HashSet Nat := {}

public abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State Grind.GrindM)

namespace VCGen

/-- Register a join-point `JumpSiteInfo` for the given fvar. Called when a
`let __do_jp := …` is detected as a shared continuation. -/
public meta def registerJP (fv : FVarId) (info : JumpSiteInfo) : _root_.VCGenM Unit :=
  modify fun s => { s with jps := s.jps.insert fv info }

/-- Look up a previously-registered join point by fvar id. -/
public meta def knownJP? (fv : FVarId) : _root_.VCGenM (Option JumpSiteInfo) :=
  return (← get).jps.get? fv

/-- True iff fuel has been exhausted (`Fuel.limited 0`). -/
public meta def outOfFuel : _root_.VCGenM Bool :=
  return match (← get).fuel with | .limited 0 => true | _ => false

/-- Decrement remaining fuel by one. No-op when fuel is `.unlimited` or already at zero. -/
public meta def burnOne : _root_.VCGenM Unit :=
  modify fun s => { s with fuel := match s.fuel with
    | .limited (n+1) => .limited n
    | other => other }

end VCGen
