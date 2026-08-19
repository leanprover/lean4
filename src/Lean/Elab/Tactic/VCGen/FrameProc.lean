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

/-- How the goal precondition frames through the frame operator: `vcgen` applies the frame rule with
the `frame` and discharges the split VC `pre ⊑ (op frame W) s⃗` with `splitVCProof?`, where `W` is
the weakest footprint the rule leaves. The procedure's remaining `subgoals` join the rule's own.
Supplying no proof leaves the split VC as one of them. -/
public structure FrameSplit where
  /-- The framed resource. A procedure that leaves it schematic surfaces that metavariable among
  its `subgoals`. -/
  frame : Expr
  /-- A proof of the split VC `pre ⊑ (op frame W) s⃗`, built against `SpecApplication.wp` for `W`. -/
  splitVCProof? : Option Expr
  /-- The unassigned subgoals of `splitVCProof?`, and any other goal the procedure leaves. -/
  subgoals : List MVarId

/-- A spec rule applied to the fresh target `?fp ⊑ wp prog ?Q E ?s⃗`. The footprint, the post and the
excess state arguments are unassigned metavariables. A `FrameInferenceProc.withSpec` assigns them:

* `excess` to the state arguments it wants the spec to run at (often the goal's own),
* `post` to the frame rule's upper-adjoint post, which the solver does when the procedure frames,
* `footprint` to the footprint it chose.

Cancelling atoms against `preVC` pins the spec's parameters, and those assignments stick. The
procedure forwards `preVC` and `subgoals` unless it discharges them itself. -/
public structure SpecApplication where
  /-- The open footprint `?fp`. -/
  footprint : MVarId
  /-- The open postcondition `?Q`. -/
  post : MVarId
  /-- The open excess state arguments `?s⃗`. -/
  excess : Array MVarId
  /-- The right-hand side `wp prog ?Q E`, before the excess state arguments apply. Once the
  procedure frames, this is the weakest footprint `W`, so a split VC proof composes `proof` under
  the frame operator. -/
  wp : Expr
  /-- The spec's precondition VC `?fp ⊑ specPre`. `specPre` carries the spec's parameter
  metavariables, so cancelling atoms against it pins them. -/
  preVC : MVarId
  /-- The spec's remaining subgoals. -/
  subgoals : List MVarId
  /-- The proof of the target entailment. -/
  proof : Expr

/-- The inputs to a `FrameInferenceProc`: the goal, how the frame was requested, and the spec being
applied. Extends the program's `wp` metadata (`WPApp`), so `Pred`, `excessArgs`, etc. are available
directly. -/
public structure FrameInferenceInfo extends WPApp where
  /-- The entailment goal `pre ⊑ wp …` the frame rule or spec applies to. -/
  goal : MVarId
  /-- The frame pinned by a matching `frames` clause, or `none` to infer the frame, e.g. from the
  precondition of the applied spec. -/
  providedFrame? : Option Expr
  /-- Declaration name of the `@[spec]` theorem being applied, `none` for a local or syntactic spec.
  A procedure can key a footprint off it, e.g. through an attribute keyed by spec name. -/
  spec? : Option Name
  /-- Builds the frame operator `op : R → Pred → Pred`, hash-consed; the selected procedure's
  `FrameProc.mkOpAppM`. -/
  mkOpApp : SymM Expr

/-- The goal's entailment relation `PartialOrder.rel α inst` (carrier and order instance applied);
apply it to two operands to build an entailment in the goal's order. -/
public def FrameInferenceInfo.le (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).stripArgsN 2

/-- What holds going in: the left-hand side of the goal entailment `pre ⊑ wp …`. -/
public def FrameInferenceInfo.pre (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).appFn!.appArg!

/-- A frame backward rule together with the positions of its assignable subgoals in the applied
rule's goal list: the schematic frame and the split VC `pre ⊑ (op frame W) s⃗`, where `W` is the
weakest footprint baked into the rule. The positions are fixed at rule construction, so applying a
`FrameSplit` assigns by index. -/
public structure FrameBackwardRule where
  /-- The backward rule concluding `pre ⊑ wp x Q E s⃗`. -/
  rule : Lean.Meta.Sym.BackwardRule
  /-- Position of the split VC `pre ⊑ (op frame W) s⃗`. -/
  splitVCIdx : Nat
  /-- Position of the schematic frame (of type `R`). -/
  frameIdx : Nat

/-- A frame inference procedure: from a `FrameInferenceInfo` (whose `providedFrame?` carries the
frame of a matching `frames` clause, if any), optionally produce a `FrameSplit`; `none` leaves the
spec to apply directly.

The constructor declares whether the procedure reads the applied spec. `pure` decides from the goal
alone, and the solver applies no spec rule before it. `withSpec` receives the spec applied to the
fresh target `?fp ⊑ wp prog ?Q E ?s⃗`, so it sees the spec's precondition in terms of the open excess
state arguments and the spec's parameters, and the solver passes an inapplicable candidate over
before the procedure runs. A `withSpec` procedure that answers `none` orphans the application, whose
metavariables are then dead. -/
public inductive FrameInferenceProc where
  /-- Decides from the goal alone. -/
  | pure (f : FrameInferenceInfo → Grind.GrindM (Option FrameSplit))
  /-- Decides from the goal and the applied spec. -/
  | withSpec (f : FrameInferenceInfo → SpecApplication → Grind.GrindM (Option FrameSplit))

/-- A frame inference procedure registered with `@[frameproc]`, together with its frame operator. The
`vcgen` frontend selects the one whose `prog` matches the goal program's monad. -/
public structure FrameProc where
  /-- Head constant of the program type (the monad) whose `wp` this procedure frames. Keys the
  procedure in the `byProg` index; `vcgen` consults it for a program with that head. -/
  prog : Name
  /-- Head constant of the frame operator, locating the split VC in the frame rule. -/
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

/-- Default frame inference procedure, agnostic of the frame operator: frame the resource pinned by
a `frames` clause, with the whole split VC deferred. -/
public def defaultFrameInferenceProc : FrameInferenceProc := .pure fun i => do
  let some frame := i.providedFrame? | return none
  return some { frame, splitVCProof? := none, subgoals := [] }

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
