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

/-- A spec rule applied to the fresh target `?fp ⊑ wp prog ?Q E ?s⃗`. The footprint `?fp`, the post
`?Q` and the excess state arguments `?s⃗` stay open, so the application binds no more than the
program determines. A procedure that frames completes the application: it assigns the excess
arguments, assigns `post` to the frame rule's upper-adjoint post, and assigns `footprint` to the
footprint it chose, so `proof` proves the footprint entailment. -/
public structure SpecApplication where
  /-- The proof of the target entailment. -/
  proof : Expr
  /-- The open footprint `?fp`. -/
  footprint : Expr
  /-- The open postcondition `?Q`. -/
  post : Expr
  /-- The right-hand side `wp prog ?Q E`, before the excess state arguments apply. Once the
  procedure frames, this is the weakest footprint the frame rule leaves, so a proof of the split
  VC composes `proof` under the frame operator. -/
  wp : Expr
  /-- The open excess state arguments `?s⃗`. -/
  excess : Array Expr
  /-- The spec's precondition VC `?fp ⊑ specPre`. `specPre` carries the spec's parameter
  metavariables, so cancelling atoms against it pins them. -/
  preVC : MVarId
  /-- The spec's remaining subgoals. -/
  subgoals : List MVarId

/-- The decision of a `FrameInferenceProc`, as data the solver carries out.

`unframed` stands down, and the solver applies the spec to the goal as-is. `framed` commits: the
solver applies the frame rule, assigns `frame` to its schematic frame, and discharges its split VC
`pre ⊑ (op frame W) s⃗` with `splitVCProof?`, or leaves the split VC as a subgoal when the
procedure supplies no proof. The returned `subgoals` join the frame condition. A procedure that
leaves its frame schematic surfaces that metavariable among its own `subgoals`. The frame rule
runs only on the `framed` path, so a stand-down costs no rule application. -/
public inductive FrameResult where
  | unframed
  | framed (frame : Expr) (splitVCProof? : Option Expr) (subgoals : List MVarId)

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

/-- A frame backward rule together with the positions of its subgoals in the applied rule's goal
list. Rule construction fixes the positions and caches them with the rule, so the solver reads the
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
frame of a matching `frames` clause, if any), decide whether to frame; see `FrameResult`. The
procedure restores any state it invalidated before it stands down.

The constructor declares whether the procedure reads the applied spec. `pure` decides from the
goal alone, and the solver applies no spec rule before it. `withSpec` receives the spec applied to
the fresh target `?fp ⊑ wp prog ?Q E ?s⃗`, so it sees the spec's precondition in terms of the open
excess state arguments and the spec's parameters, and the solver passes an inapplicable candidate
over before the procedure runs. A `withSpec` procedure that stands down orphans the application,
whose metavariables are then dead. -/
public inductive FrameInferenceProc where
  /-- Decides from the goal alone. -/
  | pure (f : FrameInferenceInfo → Grind.GrindM FrameResult)
  /-- Decides from the goal and the applied spec. -/
  | withSpec (f : FrameInferenceInfo → SpecApplication → Grind.GrindM FrameResult)

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
decomposition. Deferred framing is candidate-agnostic: the residual entailment into the weakest
footprint re-enters `solve`, and `solve` dispatches the spec candidates afresh. So this combinator
does not read the spec application. -/
public def FrameInferenceProc.ofFrame?
    (f : FrameInferenceInfo → Grind.GrindM (Option Expr)) : FrameInferenceProc :=
  .pure fun i => do
    let some frame ← f i | return .unframed
    return .framed frame none []

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
