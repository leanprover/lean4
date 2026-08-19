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
  /-- A proof of the split VC `pre ⊑ (op frame W) s⃗`, built against `SpecApp.wp` for `W`. -/
  splitVCProof? : Option Expr
  /-- The unassigned subgoals of `splitVCProof?`, and any other goal the procedure leaves. -/
  subgoals : List MVarId

/-- A spec rule applied to the target `?fp ⊑ W s⃗`, where `W` is the weakest footprint the frame
rule left. Its `WPApp` describes `W s⃗`: the post is already the frame rule's upper adjoint, and
the excess state arguments are metavariables, so only the footprint and the state are open. A
`committed` procedure assigns `footprint` to the footprint it chose, and `proof` then proves the
target. It assigns an entry of `excessArgs` only to run the spec at another state than the goal's.

The solver forwards the application's own obligations, so a procedure returns only the goals it
creates itself. -/
public structure SpecApp extends WPApp where
  /-- The open footprint `?fp`. -/
  footprint : MVarId
  /-- The spec's precondition VC `?fp ⊑ specP`. The procedure may simplify it further after
  settling `?fp`, for example by cancelling parts of it. In doing so, it may assign metavariables
  occurring in `specP`. -/
  preVC : MVarId
  /-- The proof of the target entailment. -/
  proof : Expr

/-- What a `FrameInferenceProc` learns about the goal: the entailment it splits, and how the frame
was requested. The `wp` application a procedure reasons about is the footprint target's, which
`SpecApp` carries; the goal's contributes only the three terms below. -/
public structure FrameInferenceInfo where
  /-- What holds going in: the left-hand side of the goal entailment `pre ⊑ wp …`. -/
  pre : Expr
  /-- The goal's entailment relation `PartialOrder.rel α inst`, carrier and order instance
  applied. Apply it to two operands to build an entailment in the goal's order. -/
  le : Expr
  /-- The goal's excess state arguments, the ones the split VC applies the frame operator to. -/
  excessArgs : Array Expr
  /-- The frame pinned by a matching `frames` clause, or `none` to infer the frame, e.g. from the
  precondition of the applied spec. -/
  providedFrame? : Option Expr
  /-- Declaration name of the `@[spec]` theorem being applied, `none` for a local or syntactic spec.
  A procedure can key a footprint off it, e.g. through an attribute keyed by spec name. -/
  spec? : Option Name
  /-- Builds the frame operator `op : R → Pred → Pred`, hash-consed; the selected procedure's
  `FrameProc.mkOpAppM`. -/
  mkOpApp : SymM Expr

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

The constructor says where the procedure runs relative to the frame rule. An `uncommitted`
procedure runs before it and decides whether to frame, from the goal alone, so it can still answer
`none` and leave the spec to apply as it stands. A `committed` procedure runs after the solver
applied the frame rule and the spec to the resulting footprint, so it frames by construction and
has no way to decline; it decides how to frame, reading the spec's precondition off `SpecApp`. -/
public inductive FrameInferenceProc where
  /-- Runs before the frame rule and decides whether to frame. -/
  | uncommitted (f : FrameInferenceInfo → Grind.GrindM (Option FrameSplit))
  /-- Runs after the frame rule and decides how to frame. -/
  | committed (f : FrameInferenceInfo → SpecApp → Grind.GrindM FrameSplit)

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
public def defaultFrameInferenceProc : FrameInferenceProc := .uncommitted fun i => do
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
