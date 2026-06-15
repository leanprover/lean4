/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.VCGen.Basic
public import Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.Simp.DiscrTree
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Tactic.Grind.Types

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do Lean.Elab.Tactic.Do.Internal.SpecAttr

namespace Lean.Elab.Tactic.Do.Internal

/-!
The `VCGenM` monad: its read-only `Context` (a fixed bundle of pre-built
`BackwardRule`s + user-customisable simp methods) and its mutable `State`
(rule caches, accumulated invariants/VCs, simp cache).
-/

/-- A lazily elaborated `until` pattern, stored behind an `IO.Ref` so the first `force` caches its
result. The pattern is elaborated against the monad of the first program encountered in `solve`
(supplied as the expected type). -/
public inductive UntilPatternThunk where
  /-- Not yet elaborated; `elabFn m` elaborates the pattern against the program monad `m`. -/
  | deferred (elabFn : Expr → MetaM Sym.Pattern)
  /-- Already elaborated and cached. -/
  | elaborated (pat : Sym.Pattern)

/-- Force the thunk in `ref` against the program monad `m`, elaborating, tracing, and caching the
pattern on first use; later calls return the cached pattern. -/
public def UntilPatternThunk.force (ref : IO.Ref UntilPatternThunk) (m : Expr) : MetaM Sym.Pattern := do
  match ← ref.get with
  | .elaborated pat => return pat
  | .deferred elabFn =>
    let pat ← elabFn m
    trace[Elab.Tactic.Do.vcgen] "`until` pattern elaborated to {pat.pattern}"
    ref.set (.elaborated pat)
    return pat

/--
Common metadata for a goal whose right-hand side is a weakest-precondition application
`pre ⊑ wp m Pred EPred monadInst instAL instEAL instWP α prog post epost s₁ ... sₙ`.
-/
public structure VCGen.WPInfo where
  /-- The `wp` function head, separated from its explicit core arguments. -/
  head : Expr
  /-- The ordered core arguments of the `wp` application:
  `#[m, Pred, EPred, monadInst, instAL, instEAL, instWP, α, prog, post, epost]`. -/
  args : Array Expr
  /-- Extra arguments applied after `wp … prog post epost`, usually concrete state arguments. -/
  excessArgs : Array Expr

namespace VCGen.WPInfo

/-- Monad type constructor argument of `wp`. -/
public def m (info : WPInfo) : Expr := info.args[0]!
/-- Predicate/lattice type argument of `wp`. -/
public def Pred (info : WPInfo) : Expr := info.args[1]!
/-- Exception postcondition type argument of `wp`. -/
public def EPred (info : WPInfo) : Expr := info.args[2]!
/-- `WPMonad` instance argument of `wp`. -/
public def instWP (info : WPInfo) : Expr := info.args[6]!
/-- Program expression classified by VCGen. -/
public def prog (info : WPInfo) : Expr := info.args[8]!

end VCGen.WPInfo

/-- Pre-built backward rules for the introduction steps of `solve`. -/
public structure VCGen.IntroRules where
  /-- The backward rule for `Triple.intro`. Unfolds `⦃P⦄ x ⦃Q; E⦄` into `P ⊑ wp x Q E`. -/
  tripleIntro : BackwardRule
  /-- The backward rule for `Lean.Order.le_of_forall_le`. Peels one excess state argument
  from a function-lattice entailment. -/
  stateArgIntro : BackwardRule
  /-- The backward rule for `Lean.Order.le_of_imp_top_le`. Introduces a bare pure
  precondition on the `Prop` lattice. -/
  propPreIntro : BackwardRule
  /-- The backward rule for `Lean.Order.ofProp_le`. Introduces an embedded pure
  precondition `⌜p⌝` on any complete lattice. -/
  ofPropPreIntro : BackwardRule
  /-- The backward rule for `Lean.Order.true_le_of_top_le`. Replaces a `True` precondition
  with `⊤` on the `Prop` lattice. -/
  truePreIntro : BackwardRule

public structure VCGen.Context where
  /-- Pre-built backward rules for the introduction steps of `solve`. -/
  introRules : VCGen.IntroRules
  /-- The backward rule for `Lean.Order.top_le_prop`. Strips a `(⊤ : Prop) ⊑ ·` wrapper
  from a VC before it is emitted. -/
  elimPreRule : BackwardRule
  /-- The backward rule for `And.intro`. -/
  andIntroRule : BackwardRule
  /-- The backward rule for `Lean.Order.PartialOrder.rel_refl`. Closes a reflexive
  entailment `pre ⊑ pre`. -/
  reflRule : BackwardRule
  /-- The backward rule for `meet_top_le_of_le`. Cancels a redundant `⊓ ⊤` on the left of an
  entailment, turning `P ⊓ ⊤ ⊑ Q` into `P ⊑ Q`. -/
  meetTopRule : BackwardRule
  /-- User-customizable simp methods used to pre-simplify hypotheses. -/
  hypSimpMethods : Option Sym.Simp.Methods := none
  /-- The `trivial` config option: when `true` (default), `Driver.emitVC` runs
  `solveTrivialConjuncts` to collapse trivial `And.intro` chains; when `false`, the goal is
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
  /-- The `debug` config option: when `true`, `tryApplyRule` retries failed
  `BackwardRule.apply` calls after `unfoldReducible` and reports an error when the
  retry succeeds, pinpointing missing normalization steps in `mvcgen'`. -/
  debug : Bool := false
  /-- The `internalize` config option: when `true` (default), `emitVC` and the
  multi-subgoal fork in `Driver.work` call `Grind.processHypotheses`. The tactic-mode
  entry point disables this when there is no `with` clause. -/
  internalize : Bool := true
  /-- Pre-parsed `invariants`/`invariants?` alternatives, indexed by 1-based invariant
  number. Bullet form maps positions to entries (`bullet n+1 → alt`); labelled form maps
  the parsed `inv<n>` numbers (out-of-order labels are supported). Empty when no
  `invariants` clause is provided or in `invariants?` (suggest) mode (handled separately). -/
  invariantAlts : Std.HashMap Nat Syntax := {}
  /-- The `until` pattern: when `some ref`, VC generation stops and emits the current goal as a VC
  once the program in `wp⟦e⟧` matches the (lazily elaborated) pattern, before applying a spec. -/
  untilPat? : Option (IO.Ref UntilPatternThunk) := none

public structure VCGen.Scope where
  /-- Spec database in scope: globals plus locals from in-scope hypotheses. -/
  specs : SpecTheorems
  /-- `__do_jp` fvars currently in scope. -/
  jps : FVarIdMap JumpSiteInfo := {}
  /-- The most recently lifted pure precondition. `tryLiftedHyp` closes handoff VCs against
  it without walking the local context. -/
  lastLiftedPre? : Option FVarId := none
  /-- Index of the next local declaration to consider for local specs. -/
  nextDeclIdx : Nat := 0
  deriving Inhabited

public structure VCGen.State where
  /--
  A cache mapping registered SpecThms to their backward rule to apply.
  The particular rule depends on the theorem name, the `WPMonad` instance and the number of
  excess state arguments that the weakest precondition target is applied to.
  -/
  specBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /--
  A cache mapping matchers to their splitting backward rule to apply.
  The particular rule depends on the matcher name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  splitBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /--
  A cache mapping lattice connectives to their backward rule to apply.
  The particular rule depends on the rule name, the monad, and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  latticeBackwardRuleCache : Std.HashMap (Name × Array Expr × Nat) BackwardRule := {}
  /--
  Holes of type `Invariant` that have been generated so far.
  -/
  invariants : Array MVarId := #[]
  /--
  The verification conditions that have been generated so far. Each entry
  shares the parent `Grind.Goal`'s state.
  -/
  vcs : Array Grind.Goal := #[]
  /--
  Persistent cache for the `Sym.Simp` simplifier used to pre-simplify hypotheses
  before grind internalization. Threading this cache across VCGen iterations avoids
  re-simplifying shared subexpressions (e.g., `s + 1 + 1 + ...` chains).
  -/
  simpState : Sym.Simp.State := {}
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

public def Scope.registerJP (s : Scope) (fv : FVarId) (info : JumpSiteInfo) : Scope :=
  { s with jps := s.jps.insert fv info }

public def Scope.knownJP? (s : Scope) (fv : FVarId) : Option JumpSiteInfo :=
  s.jps.get? fv

public def Scope.insertSpec (s : Scope) (thm : SpecTheorem) : Scope :=
  { s with specs := s.specs.insert thm }

/-- Walk `goal`'s local context from `scope.nextDeclIdx` onward, registering any
spec-shaped hypotheses as local specs. Advances `nextDeclIdx` to the current
context size so siblings share work. -/
public def Scope.collectLocalSpecs (scope : Scope) (goal : MVarId) : VCGenM Scope :=
  goal.withContext do
    let lctx ← getLCtx
    if scope.nextDeclIdx == lctx.decls.size then return scope
    let scope ← lctx.foldlM (init := scope) (start := scope.nextDeclIdx) fun scope decl => do
      if decl.isAuxDecl then return scope
      try
        if let some thm ← mkSpecTheoremFromLocal decl.fvarId (eval_prio low) then
          return scope.insertSpec thm
      catch _ => pure ()
      return scope
    return { scope with nextDeclIdx := lctx.decls.size }

/-- True iff fuel has been exhausted (`Fuel.limited 0`). -/
public def outOfFuel : VCGenM Bool :=
  return match (← get).fuel with | .limited 0 => true | _ => false

/-- Decrement remaining fuel by one. No-op when fuel is `.unlimited` or already at zero. -/
public def burnOne : VCGenM Unit :=
  modify fun s => { s with fuel := match s.fuel with
    | .limited (n+1) => .limited n
    | other => other }

end VCGen

end Lean.Elab.Tactic.Do.Internal
