/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.VCGen.WPApp
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.AlphaShareBuilder
public import Lean.Meta.Tactic.Grind.Types
import Std.Internal.Order.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Tactic.Util

/-!
The metadata a frame inference procedure operates on: the `wp` application metadata `WPApp` and the
`FrameProc` bundling an inference procedure with its frame operator.
`@[frameproc]` registration lives in `FrameProcAttr`.
-/

open Lean Meta Sym Sym.Internal

namespace Lean.Elab.Tactic.VCGen

/-- The subgoals of the frame rule `commit` applied, by role. -/
public structure FrameGoals where
  /-- The schematic frame `?F : R`. -/
  frame : MVarId
  /-- The split VC `pre ⊑ (op ?F W) s⃗`, where `W = wp prog (fun a => upperAdjoint (op ?F) (Q a)) E`
  is the weakest footprint. A residual entailment into `W` left as a subgoal re-enters `solve`,
  which applies the spec to it; the spec's precondition VC then closes by unification against the
  footprint the procedure chose, pinning the spec's parameters. -/
  splitVC : MVarId
  /-- The frame condition `WP.Frames op prog ?F`. -/
  frames : MVarId

/-- The weakest footprint `W` of the committed split VC `pre ⊑ (op ?F W) s⃗`, with `numExcess` the
number of excess state arguments `s⃗`. -/
public def FrameGoals.weakestFootprint (goals : FrameGoals) (numExcess : Nat) : SymM Expr :=
  return ((← goals.splitVC.getType).appArg!.stripArgsN numExcess).appArg!

/-- Discharge the split VC with `proof`, framing `frame`; the returned subgoals are `subgoals` and
the frame condition. -/
public def FrameGoals.withDischargedSplitVC (goals : FrameGoals) (frame proof : Expr)
    (subgoals : List MVarId := []) : Grind.GrindM (List MVarId) := do
  goals.frame.assign (← shareCommon frame)
  goals.splitVC.assign proof
  return subgoals ++ [goals.frames]

/-- Frame `frame` with the whole split VC left as a subgoal. -/
public def FrameGoals.withDeferredSplitVC (goals : FrameGoals) (frame : Expr) :
    Grind.GrindM (List MVarId) := do
  goals.frame.assign (← shareCommon frame)
  return [goals.splitVC, goals.frames]

/-- The inputs to a `FrameInferenceProc`: the goal, how the frame was requested, and the spec being
applied. Extends the program's `wp` metadata (`WPApp`), so `Pred`, `excessArgs`, etc. are available
directly. -/
public structure FrameInferenceInfo extends WPApp where
  /-- The entailment goal `pre ⊑ wp …` the frame rule or spec applies to. -/
  goal : MVarId
  /-- The frame pinned by a matching `frames` clause, or `none` to infer the frame, e.g. from the
  precondition or from `peekSpecPre`. -/
  providedFrame? : Option Expr
  /-- Declaration name of the `@[spec]` theorem being applied, `none` for a local or syntactic spec.
  A procedure can key a footprint off it, e.g. through an attribute keyed by spec name. -/
  spec? : Option Name
  /-- Applies the backward rule of the `@[spec]` theorem being applied to a goal of the
  procedure's choosing. A `.failed` result leaves no observable state behind. -/
  applySpec : MVarId → Grind.GrindM Lean.Meta.Sym.ApplyResult
  /-- Builds the frame operator `op : R → Pred → Pred`, hash-consed; the selected procedure's
  `FrameProc.mkOpAppM`. -/
  mkOpApp : SymM Expr
  /-- Commits the goal to the frame rule: applies it, assigning `goal`, and returns its subgoals by
  role. The point of no return: whatever the procedure leaves unassigned in the goal's proof becomes
  a subgoal. -/
  commit : Grind.GrindM FrameGoals

/-- The goal's entailment relation `PartialOrder.rel α inst` (carrier and order instance applied);
apply it to two operands to build an entailment in the goal's order. -/
public def FrameInferenceInfo.le (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).stripArgsN 2

/-- What holds going in: the left-hand side of the goal entailment `pre ⊑ wp …`. -/
public def FrameInferenceInfo.pre (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).appFn!.appArg!

/-- A frame backward rule together with the positions of its subgoals in the applied rule's goal
list. The positions are fixed at rule construction and cached with the rule, so `commit` reads the
subgoals off by index. -/
public structure FrameBackwardRule where
  /-- The backward rule concluding `pre ⊑ wp x Q E s⃗`. -/
  rule : Lean.Meta.Sym.BackwardRule
  /-- Position of the split VC `pre ⊑ (op frame W) s⃗`. -/
  splitVCIdx : Nat
  /-- Position of the schematic frame (of type `R`). -/
  frameIdx : Nat
  /-- Position of the frame condition `WP.Frames op x frame`. -/
  framesIdx : Nat

/-- A frame inference procedure: from a `FrameInferenceInfo` (whose `providedFrame?` carries the
frame of a matching `frames` clause, if any), decide whether to frame. Framing means calling
`i.commit`, assigning the returned schematic frame, discharging as much of the split VC as the
procedure can, and returning the subgoals left over, including any of its own making. Leaving the
goal unassigned applies the spec unframed instead. `none` forwards a `.failed` result of
`i.applySpec`: the spec does not apply, and the solver passes the candidate over. The procedure
restores any state it invalidated before standing down either way. -/
public abbrev FrameInferenceProc :=
  FrameInferenceInfo → Grind.GrindM (Option (List MVarId))

/-- How to decompose a lattice operator `head … s⃗` on the RHS of an entailment: the distribution and
unfolding `rewrites` that saturate it, and the terminal `⊑`-introduction `terminals` that close the
reduced form. `head` keys the split in the `latticeOps` table. -/
public structure LatticeOp where
  /-- Head constant of the operator this split decomposes. Keys the `latticeOps` table. -/
  head : Name
  /-- The number of leading arguments held constant during rule construction: the operator's carrier
  type and its typeclass instances. The operands and excess state arguments after them become the
  rule's schematic parameters. `2` for a connective over a `CompleteLattice` carrier; `0` for a
  monomorphic operator. -/
  numConst : Nat := 2
  /-- Distribution and unfolding equalities that saturate the operator applied to state arguments. -/
  rewrites : Array Name := #[]
  /-- The operator's terminal `⊑`-introduction rule, or `none` when it saturates to another operator's
  terminal. -/
  terminal? : Option Name := none

/-- A frame inference procedure registered with `@[frameproc]`, together with its frame operator. The
`vcgen` frontend selects the one whose `prog` matches the goal program's monad. -/
public structure FrameProc where
  /-- Head constant of the program type (the monad) whose `wp` this procedure frames. Keys the
  procedure in the `byProg` index; `vcgen` consults it for a program with that head. -/
  prog : Name
  /-- Head constant of the frame operator, locating the split VC among the frame rule's subgoals. -/
  opHead : Name
  /-- Builds the frame operator (head constant `opHead`) applied to the goal's assertion type. -/
  mkOpAppM : WPApp → MetaM Expr
  /-- The resource type `R` of the operator `op : R → Pred → Pred`, i.e. the domain of `mkOpAppM`'s
  result. Provided directly so `vcgen` reads it without building the operator, which it does only when
  a frame actually applies. -/
  mkResourceTy : WPApp → MetaM Expr
  /-- The frame inference metaprogram. -/
  proc : FrameInferenceProc

/-- The registered frame inference procedures, indexed by the program monad's head constant
(selected per node in `solve`). -/
public structure FrameProcs where
  byProg : Std.HashMap Name FrameProc := {}

public instance : Inhabited FrameProcs := ⟨{}⟩

public def FrameProcs.insert (s : FrameProcs) (fp : FrameProc) : FrameProcs :=
  { byProg := s.byProg.insert fp.prog fp }

/-- The procedure framing `frame` with the whole split VC left as a subgoal for the built-in lattice
decomposition: check that the spec applies, commit, assign the schematic frame, discharge nothing. -/
public def FrameInferenceProc.ofFrame?
    (f : FrameInferenceInfo → Grind.GrindM (Option Expr)) : FrameInferenceProc :=
  fun i => do
    let some frame ← f i | return (some [])
    -- The spec must apply for the framing to mean anything; probing a copy of the goal leaves no
    -- observable state behind.
    let probe ← mkFreshExprSyntheticOpaqueMVar (← i.goal.getType)
    let .goals _ ← i.applySpec probe.mvarId! | return none
    some <$> (← i.commit).withDeferredSplitVC frame

/-- Default frame inference procedure, agnostic of the frame operator: frame the resource pinned by
a `frames` clause, with the whole split VC deferred. -/
public def defaultFrameInferenceProc : FrameInferenceProc :=
  .ofFrame? fun i => pure i.providedFrame?

/-- The lattice meet operator over the goal's assertion type. -/
private def meetOp (info : WPApp) : MetaM Expr :=
  Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]

/-- The default frame operator: lattice meet `pre ⊓ frame`, the Hoare frame every complete lattice carries.
Framed only through an explicit `frames` clause; used for a monad with no registered `@[frameproc]`. -/
public def meetFrameProc : FrameProc where
  prog := ``Lean.Order.meet
  mkOpAppM := meetOp
  mkResourceTy info := pure info.Pred
  opHead := ``Lean.Order.meet
  proc := defaultFrameInferenceProc

end Lean.Elab.Tactic.VCGen
