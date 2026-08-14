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

/-- The subgoals of the applied frame rule, by role. -/
public structure FrameGoals where
  /-- The schematic frame `?F : R`. -/
  frame : MVarId
  /-- The split VC `pre ⊑ (op ?F W) s⃗`, where `W = wp prog (fun a => upperAdjoint (op ?F) (Q a)) E`
  is the weakest footprint. A residual entailment into `W` left as a subgoal re-enters `solve`,
  which applies the spec to it. The spec's precondition VC then closes by unification against the
  footprint the procedure chose, and this pins the spec's parameters. -/
  splitVC : MVarId
  /-- The frame condition `WP.Frames op prog ?F`. -/
  frames : MVarId

/-- The weakest footprint `W` of the committed split VC `pre ⊑ (op ?F W) s⃗`, with `numExcess` the
number of excess state arguments `s⃗`. -/
public def FrameGoals.weakestFootprint (goals : FrameGoals) (numExcess : Nat) : SymM Expr :=
  return ((← goals.splitVC.getType).appArg!.stripArgsN numExcess).appArg!

/-- Discharge the split VC with `proof` and frame `frame`. The returned subgoals are `subgoals`
and the frame condition. -/
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

/-- A spec rule applied to a fresh footprint entailment `?fp ⊑ wp prog ?post epost s⃗`, with the
footprint `?fp` and the post `?post` left open. This application settles applicability, but it
binds no more than the program determines. A procedure completes it after `commit` in two
assignments.
`post` gets the upper-adjoint post of the frame rule, so `proof` proves the footprint entailment
into the weakest footprint `W`. `footprint` gets the footprint the procedure chose. -/
public structure SpecApplication where
  /-- The proof of the footprint entailment. -/
  proof : Expr
  /-- The open footprint `?fp`. -/
  footprint : Expr
  /-- The open postcondition `?post`. -/
  post : Expr
  /-- The spec's precondition VC `?fp ⊑ specPre`. `specPre` carries the spec's parameter
  metavariables, so cancelling atoms against it pins them. -/
  preVC : MVarId
  /-- The spec's remaining subgoals. -/
  subgoals : List MVarId

/-- The inputs to a `FrameInferenceProc`: the goal, how the frame was requested, and the spec being
applied. Extends the program's `wp` metadata (`WPApp`), so `Pred`, `excessArgs`, etc. are available
directly. -/
public structure FrameInferenceInfo extends WPApp where
  /-- The entailment goal `pre ⊑ wp …` the frame rule or spec applies to. -/
  goal : MVarId
  /-- The frame a matching `frames` clause pins, or `none` to infer the frame, for example from
  the precondition of the applied spec. -/
  providedFrame? : Option Expr
  /-- Declaration name of the `@[spec]` theorem being applied, `none` for a local or syntactic spec.
  A procedure can key a footprint off it, for example through an attribute keyed by spec name. -/
  spec? : Option Name
  /-- Applies the backward rule of the `@[spec]` theorem to a fresh footprint entailment
  `?fp ⊑ wp prog ?post epost s⃗`. The footprint and the post stay open. The procedure supplies the
  excess state arguments `s⃗`. The rule fixes their count to the goal's count, and their values
  are free, with `excessArgs` as the goal's own. `none` means the rule does not apply, and the
  failed attempt leaves no observable state behind. The successful application is an orphan until
  the procedure completes it, so a procedure that stands down can forget it. -/
  applySpec : Array Expr → Grind.GrindM (Option SpecApplication)
  /-- Builds the frame operator `op : R → Pred → Pred`, hash-consed; the selected procedure's
  `FrameProc.mkOpAppM`. -/
  mkOpApp : SymM Expr
  /-- Commits the goal to the frame rule: applies the rule, assigns `goal`, and returns the
  subgoals by role. This is the point of no return: whatever the procedure leaves unassigned in
  the goal's proof becomes a subgoal. -/
  commit : Grind.GrindM FrameGoals

/-- The goal's entailment relation `PartialOrder.rel α inst` (carrier and order instance applied);
apply it to two operands to build an entailment in the goal's order. -/
public def FrameInferenceInfo.le (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).stripArgsN 2

/-- What holds going in: the left-hand side of the goal entailment `pre ⊑ wp …`. -/
public def FrameInferenceInfo.pre (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).appFn!.appArg!

/-- A frame backward rule together with the positions of its subgoals in the applied rule's goal
list. Rule construction fixes the positions and caches them with the rule, so `commit` reads the
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
frame of a matching `frames` clause, if any), decide whether to frame. To frame, the procedure
calls `i.commit`, assigns the schematic frame, discharges what it can of the split VC, and
returns the remaining subgoals. If the procedure leaves the goal unassigned, the solver applies
the spec unframed. `.failed` forwards a failed `i.applySpec`: the
spec does not apply, and the solver passes the candidate over. The procedure restores any state it
invalidated before it stands down. -/
public abbrev FrameInferenceProc :=
  FrameInferenceInfo → Grind.GrindM Sym.ApplyResult

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

/-- The procedure that frames `frame` and leaves the whole split VC to the built-in lattice
decomposition: commit, assign the schematic frame, discharge nothing. Deferred framing is
candidate-agnostic: the residual entailment into the weakest footprint re-enters `solve`, and
`solve` dispatches the spec candidates afresh. So this combinator does not test applicability. -/
public def FrameInferenceProc.ofFrame?
    (f : FrameInferenceInfo → Grind.GrindM (Option Expr)) : FrameInferenceProc :=
  fun i => do
    let some frame ← f i | return (.goals [])
    .goals <$> (← i.commit).withDeferredSplitVC frame

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
