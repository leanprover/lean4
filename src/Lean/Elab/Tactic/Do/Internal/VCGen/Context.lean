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

/-- A value elaborated lazily in `MetaM` against the monad of the first program encountered in
`solve` (supplied as the expected type), then cached. Used for the `until` pattern
(`Deferred Sym.Pattern`, behind an `IO.Ref` in the `Context`) and the `frames` database
(`Deferred FrameDB`, in the `State`). -/
public inductive Deferred (α : Type) where
  /-- Not yet elaborated; `elabFn m` elaborates against the program monad `m`. -/
  | deferred (elabFn : Expr → MetaM α)
  /-- Already elaborated and cached. -/
  | elaborated (value : α)

/-- Force `d` against the program monad `m`, elaborating on first use and caching the result via
`writeback`; later calls return the cached value. `writeback` stores into the slot `d` came from:
an `IO.Ref.set` for the `until` pattern in the `Context`, a `modify` for the `frames` `State` field. -/
public def Deferred.force {α : Type} {n : Type → Type} [Monad n] [MonadLiftT MetaM n]
    (d : Deferred α) (writeback : Deferred α → n Unit) (m : Expr) : n α := do
  match d with
  | .elaborated a => return a
  | .deferred elabFn =>
    let a ← elabFn m
    writeback (.elaborated a)
    return a

/-- A single elaborated `frames` alternative: its program pattern, the binder name of each pattern
variable (`none` for `_`, index-aligned with `pat.varTypes`), the raw frame term (elaborated in the
matched goal's context), the source position (a precedence tiebreak among matches, and its index
into `FrameDB.entries`), and whether it has already been applied. -/
public structure FrameEntry where
  pat : Sym.Pattern
  varNames : Array (Option Name)
  frameStx : Syntax
  srcIdx : Nat
  /-- Set once this alternative has been applied, so it frames at most one occurrence. -/
  retired : Bool := false
  deriving Inhabited

/-- The materialized frame database: program patterns keyed in a discrimination tree to the `srcIdx`
of the matching alternative, alongside the alternatives themselves in source order. Materialized once
in `State.frameDB?`; thereafter only the `retired` flags of `entries` change. -/
public structure FrameDB where
  tree : DiscrTree Nat := .empty
  entries : Array FrameEntry := #[]

/--
Common metadata for a goal whose right-hand side is a weakest-precondition application
`pre ⊑ wp Prog Value Pred EPred instAL instEAL instWP prog post epost s₁ ... sₙ`.
-/
public structure VCGen.WPInfo where
  /-- The `wp` function head, separated from its explicit core arguments. -/
  head : Expr
  /-- The ordered core arguments of the `wp` application:
  `#[Prog, Value, Pred, EPred, instAL, instEAL, instWP, prog, post, epost]`. -/
  args : Array Expr
  /-- Extra arguments applied after `wp … prog post epost`, usually concrete state arguments. -/
  excessArgs : Array Expr

namespace VCGen.WPInfo

/-- Program type argument of `wp` (e.g. `m α` or a non-monadic program type). -/
public def progTy (info : WPInfo) : Expr := info.args[0]!
/-- The monad of an `m α`-shaped program type, obtained by dropping the value type `α`. For a
non-monadic program type the type itself is returned. -/
public def m (info : WPInfo) : Expr :=
  if info.args[0]!.isApp then info.args[0]!.appFn! else info.args[0]!
/-- Result/value type argument of `wp`. -/
public def Value (info : WPInfo) : Expr := info.args[1]!
/-- Predicate/lattice type argument of `wp`. -/
public def Pred (info : WPInfo) : Expr := info.args[2]!
/-- Exception postcondition type argument of `wp`. -/
public def EPred (info : WPInfo) : Expr := info.args[3]!
/-- `WP` instance argument of `wp`. -/
public def instWP (info : WPInfo) : Expr := info.args[6]!
/-- Program expression classified by VCGen. -/
public def prog (info : WPInfo) : Expr := info.args[7]!

end VCGen.WPInfo

/-- Pre-built backward rules used by `solve`. -/
public structure VCGen.BackwardRules where
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
  /-- The backward rule for `Lean.Order.top_le_prop`. Strips a `(⊤ : Prop) ⊑ ·` wrapper
  from a VC before it is emitted. -/
  elimPre : BackwardRule
  /-- The backward rule for `And.intro`. -/
  andIntro : BackwardRule
  /-- The backward rule for `Lean.Order.PartialOrder.rel_refl`. Closes a reflexive
  entailment `pre ⊑ pre`. -/
  refl : BackwardRule
  /-- The backward rule for `meet_top_le_of_le`. Cancels a redundant `⊓ ⊤` on the left of an
  entailment, turning `P ⊓ ⊤ ⊑ Q` into `P ⊑ Q`. -/
  meetTop : BackwardRule

/-- Build the backward rules used by `solve` from their underlying lemmas. -/
public def VCGen.mkBackwardRules : MetaM VCGen.BackwardRules := do
  return {
    tripleIntro := ← mkBackwardRuleFromDecl ``Std.Internal.Do.Triple.intro
    stateArgIntro := ← mkBackwardRuleFromDecl ``Lean.Order.le_of_forall_le
    propPreIntro := ← mkBackwardRuleFromDecl ``Lean.Order.le_of_imp_top_le
    ofPropPreIntro := ← mkBackwardRuleFromDecl ``Lean.Order.ofProp_le
    truePreIntro := ← mkBackwardRuleFromDecl ``Lean.Order.true_le_of_top_le
    elimPre := ← mkBackwardRuleFromDecl ``Lean.Order.top_le_prop
    andIntro := ← mkBackwardRuleFromDecl ``And.intro
    refl := ← mkBackwardRuleFromDecl ``Lean.Order.PartialOrder.rel_refl
    meetTop := ← mkBackwardRuleFromDecl ``Std.Internal.Do.CompleteLattice.meet_top_le_of_le
  }

public structure VCGen.Context where
  /-- Pre-built backward rules used by `solve`. -/
  backwardRules : VCGen.BackwardRules
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
  /-- The `errorOnMissingSpec` config option: when `true` (default), a program with no matching
  spec raises a hard error. When `false`, the goal is emitted as an unsolved VC for the user to
  discharge — useful with `vcgen [-some_spec]` patterns where the user knows the spec is
  intentionally removed and wants to handle the residual goal by hand. -/
  errorOnMissingSpec : Bool := true
  /-- The `debug` config option: when `true`, `tryApplyRule` retries failed
  `BackwardRule.apply` calls after `unfoldReducible` and reports an error when the
  retry succeeds, pinpointing missing normalization steps in `vcgen`. -/
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
  untilPat? : Option (IO.Ref (Deferred Sym.Pattern)) := none

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

  The instance is keyed by `ExprPtr`, so lookups compare it by pointer rather than structurally.
  This is sound because the instance is a subterm of the hash-consed goal target.
  -/
  specBackwardRuleCache : Std.HashMap (Name × ExprPtr × Nat) BackwardRule := {}
  /--
  A cache mapping matchers to their splitting backward rule to apply.
  The particular rule depends on the matcher name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.

  The instance is keyed by `ExprPtr`, so lookups compare it by pointer rather than structurally.
  This is sound because the instance is a subterm of the hash-consed goal target.
  -/
  splitBackwardRuleCache : Std.HashMap (Name × ExprPtr × Nat) BackwardRule := {}
  /--
  A cache mapping lattice connectives to their backward rule to apply.
  The particular rule depends on the rule name, the monad, and the number of excess state
  arguments that the weakest precondition target is applied to.

  The argument types are keyed by `ExprPtr`, so lookups compare them by pointer rather than
  structurally. This is sound because they are subterms of the hash-consed goal target.
  -/
  latticeBackwardRuleCache : Std.HashMap (Name × Array ExprPtr × Nat) BackwardRule := {}
  /--
  The frame database, elaborated lazily against the first program's monad on first use. The
  discrimination tree is fixed; a matched alternative is retired in place by setting
  `FrameEntry.retired`, so each applies at most once (first match wins) and a program whose
  alternative is retired is framed no further and reaches the normal `applySpec` path.
  -/
  frameDB? : Option (Deferred FrameDB) := none
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
