/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.WPApp
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.AlphaShareBuilder
import Std.Internal.Do.Order.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.AbstractMVars
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Tactic.Util

/-!
The metadata a frame inference procedure operates on: the `wp` application metadata `WPApp` and the
`FrameProc` bundling an inference procedure with its frame operator.
`@[frameproc]` registration lives in `FrameProcAttr`.
-/

open Lean Meta Sym Sym.Internal

namespace Lean.Elab.Tactic.Do.Internal

/-- How the goal precondition frames through the frame operator: `vcgen` applies the frame rule with
the `frame`, discharging the split VC `pre ⊑ (op frame residualPre) s⃗` with `proof` and leaving
`proof`'s `subgoals`. `residualPre` is the solver-owned metavariable for the residual precondition,
which the solver fills after the frame rule applies.

Build a `FrameSplit` with `FrameSplit.withDischargedSplitVC` (proof supplied) or
`FrameSplit.withDeferredSplitVC` (split VC left as one subgoal). -/
public structure VCGen.FrameSplit where
  /-- The framed resource. -/
  frame : Expr
  /-- A proof of the split VC `pre ⊑ (op frame residualPre) s⃗`. -/
  splitVCProof : Expr
  /-- The unassigned subgoals of `splitVCProof`. -/
  subgoals : List MVarId

/-- The inputs to a `FrameInferenceProc`: the goal, how the frame was requested, the spec being
applied, and the residual metavariable. Extends the program's `wp` metadata (`WPApp`), so `Pred`,
`excessArgs`, etc. are available directly. -/
public structure VCGen.FrameInferenceInfo extends VCGen.WPApp where
  /-- The entailment goal `pre ⊑ wp …` the frame rule or spec applies to. -/
  goal : MVarId
  /-- The frame pinned by a matching `frames` clause, or `none` to infer the frame, e.g. from the
  precondition or from `specPre?`. -/
  providedFrame? : Option Expr
  /-- Declaration name of the `@[spec]` theorem being applied, `none` for a local or syntactic spec.
  A procedure can key a footprint off it, e.g. through an attribute keyed by spec name. -/
  spec? : Option Name
  /-- The backward rule of the `@[spec]` theorem being applied. -/
  specRule : Lean.Meta.Sym.BackwardRule
  /-- The residual precondition the program runs against once `frame` is framed off: in the split VC
  `pre ⊑ op frame residualPre`, the complement of `frame` in `pre`. A solver-owned synthetic-opaque
  metavariable the procedure must not assign; the solver fills it once the frame rule fixes it. -/
  residualPre : Expr

/-- The goal's entailment relation `PartialOrder.rel α inst` (carrier and order instance applied);
apply it to two operands to build an entailment in the goal's order. -/
public def VCGen.FrameInferenceInfo.le (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).stripArgsN 2

/-- What holds going in: the left-hand side of the goal entailment `pre ⊑ wp …`. -/
public def VCGen.FrameInferenceInfo.pre (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).appFn!.appArg!

/-- The spec precondition instantiated at the call site, read off a speculative application of
`specRule` to `goal` that is rolled back: the precondition VC's metavariables are frozen into a
telescope and reopened fresh in the restored context, so they outlive the rollback. `none` when the
rule does not apply or leaves no precondition VC. -/
public def VCGen.FrameInferenceInfo.specPre? (i : FrameInferenceInfo) : SymM (Option Expr) := do
  let saved ← Meta.saveState
  let .goals subgoals ← i.specRule.apply i.goal | return none
  -- The precondition VC is the bare `pre ⊑ specPre` premise among the subgoals; the post and
  -- exception VCs are `∀`-quantified.
  let specPre? ← subgoals.findSomeM? fun g => do
    let ty ← g.getType
    let_expr Lean.Order.PartialOrder.rel _ _ _ specPre := ty | return none
    -- Resolve only an assigned head mvar so the procedure's head test (`isAppOf`) sees the real
    -- operator; nested mvars are resolved by the procedure's own unification.
    return some (← instantiateMVarsIfMVarAppS specPre)
  let some specPre := specPre? | do saved.restore; return none
  let abs ← Meta.abstractMVars (← instantiateMVarsS specPre)
  saved.restore
  let (_, _, specPre) ← Meta.openAbstractMVarsResult abs
  return some (← shareCommon specPre)

/-- The split VC proposition `pre ⊑ (op frame footprint) s⃗`: the frame operator `op : R → Pred → Pred`
applied to `frame` and `footprint`, then to the excess state arguments, entailed by `pre` in the
goal's order. `op`, `frame` and `footprint` must be hash-consed (`shareCommon`); the result is. -/
public def VCGen.FrameInferenceInfo.mkSplitVCS (i : FrameInferenceInfo) (op frame footprint : Expr) :
    SymM Expr := do
  let rhs ← mkAppNS (← mkAppNS op #[frame, footprint]) i.excessArgs
  mkAppNS (← i.le) #[← i.pre, rhs]

/-- A `FrameSplit` framing `frame` whose split VC `pre ⊑ (op frame residualPre) s⃗` is deferred as a
fresh subgoal for the built-in lattice (meet) decomposition to split. -/
public def VCGen.FrameSplit.withDeferredSplitVC (i : FrameInferenceInfo) (op frame : Expr) :
    SymM FrameSplit := do
  let m ← mkFreshExprSyntheticOpaqueMVar (← i.mkSplitVCS op frame i.residualPre)
  return { frame, splitVCProof := m, subgoals := [m.mvarId!] }

/-- A `FrameSplit` framing `frame`, discharging the split VC `pre ⊑ (op frame residualPre) s⃗` with
`splitVCProof` and leaving its `subgoals`. -/
public def VCGen.FrameSplit.withDischargedSplitVC (frame splitVCProof : Expr)
    (subgoals : List MVarId := []) : FrameSplit :=
  { frame, splitVCProof, subgoals }

/-- A frame backward rule together with the positions of its assignable subgoals in the applied
rule's goal list: the schematic frame and the split VC `pre ⊑ (op frame W) s⃗`, where `W` is the
weakest footprint baked into the rule. The positions are fixed at rule construction, so applying a
`FrameSplit` assigns by index. -/
public structure VCGen.FrameBackwardRule where
  /-- The backward rule concluding `pre ⊑ wp x Q E s⃗`. -/
  rule : Lean.Meta.Sym.BackwardRule
  /-- Position of the split VC `pre ⊑ (op frame W) s⃗`. -/
  splitVCIdx : Nat
  /-- Position of the schematic frame (of type `R`). -/
  frameIdx : Nat

/-- A frame inference procedure: from a `FrameInferenceInfo` (whose `providedFrame?` carries the
frame of a matching `frames` clause, if any), optionally produce a `FrameSplit`; `none` leaves the
spec to apply directly.

The procedure produces the frame and a proof of the split VC `pre ⊑ (op frame residualPre) s⃗`; it
must not assign `residualPre`, which the solver fills with the weakest footprint after the frame rule
applies. Build the result with `FrameSplit.withDischargedSplitVC` (proof supplied) or
`FrameSplit.withDeferredSplitVC` (split VC left as a subgoal). -/
public abbrev VCGen.FrameInferenceProc :=
  VCGen.FrameInferenceInfo → SymM (Option VCGen.FrameSplit)

/-- How to decompose a lattice operator `head … s⃗` on the RHS of an entailment: the distribution and
unfolding `rewrites` that saturate it, and the terminal `⊑`-introduction `terminals` that close the
reduced form. `head` keys the split in the `latticeOps` table. -/
public structure VCGen.LatticeOp where
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
public structure VCGen.FrameProc where
  /-- Head constant of the program type (the monad) whose `wp` this procedure frames. Keys the
  procedure in the `byProg` index; `vcgen` consults it for a program with that head. -/
  prog : Name
  /-- Head constant of the frame operator, locating the split VC in the frame rule. -/
  opHead : Name
  /-- Builds the frame operator (head constant `opHead`) applied to the goal's assertion type. -/
  mkOpAppM : VCGen.WPApp → MetaM Expr
  /-- The resource type `R` of the operator `op : R → Pred → Pred`, i.e. the domain of `mkOpAppM`'s
  result. Provided directly so `vcgen` reads it without building the operator, which it does only when
  a frame actually applies. -/
  mkResourceTy : VCGen.WPApp → MetaM Expr
  /-- The frame inference metaprogram. -/
  proc : VCGen.FrameInferenceProc

/-- The registered frame inference procedures, indexed by the program monad's head constant
(selected per node in `solve`). -/
public structure VCGen.FrameProcs where
  byProg : Std.HashMap Name VCGen.FrameProc := {}

public instance : Inhabited VCGen.FrameProcs := ⟨{}⟩

public def VCGen.FrameProcs.insert (s : FrameProcs) (fp : FrameProc) : FrameProcs :=
  { byProg := s.byProg.insert fp.prog fp }

/-- Default frame inference procedure, agnostic of the frame operator: frame the resource pinned by
a `frames` clause, with the weakest footprint. `mkOp` builds the frame operator, invoked only when a
frame is pinned. -/
public def VCGen.defaultFrameInferenceProc (mkOp : WPApp → MetaM Expr) : FrameInferenceProc :=
  fun i => do
    let some frame := i.providedFrame? | return none
    return some (← FrameSplit.withDeferredSplitVC i (← shareCommon (← mkOp i.toWPApp)) frame)

/-- The lattice meet operator over the goal's assertion type. -/
private def meetOp (info : VCGen.WPApp) : MetaM Expr :=
  Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]

/-- The default frame operator: lattice meet `pre ⊓ frame`, the Hoare frame every complete lattice carries.
Framed only through an explicit `frames` clause; used for a monad with no registered `@[frameproc]`. -/
public def VCGen.meetFrameProc : VCGen.FrameProc where
  prog := ``Lean.Order.meet
  mkOpAppM := meetOp
  mkResourceTy info := pure info.Pred
  opHead := ``Lean.Order.meet
  proc := defaultFrameInferenceProc meetOp

end Lean.Elab.Tactic.Do.Internal
