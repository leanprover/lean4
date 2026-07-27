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
import Lean.Meta.Sym.InferType
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

/-- How the frame was requested: an `explicit` resource pinned by a `frames` clause, or the
`implicit` spec precondition to infer the frame from. -/
public inductive VCGen.FrameInferenceHint where
  /-- Frame the given resource, pinned by a `frames` clause. -/
  | explicit (frame : Expr)
  /-- Infer the frame from the spec's precondition `specPre`, the right-hand side of the spec's
  precondition VC `pre ⊑ specPre`. -/
  | implicit (specPre : Expr)

/-- The inputs to a `FrameInferenceProc`: the frame operator, the goal entailment relation, the
precondition, how the frame was requested, and the residual metavariable. Extends the program's `wp`
metadata (`WPApp`), so `Pred`, `excessArgs`, etc. are available directly. -/
public structure VCGen.FrameInferenceInfo extends VCGen.WPApp where
  /-- The applicable frame operator `op : R → Pred → Pred`. -/
  op : Expr
  /-- The goal's entailment relation `PartialOrder.rel α inst` (carrier and order instance applied);
  apply it to two operands to build an entailment in the goal's order. -/
  le : Expr
  /-- What holds going in: the left-hand side of the goal entailment `pre ⊑ wp …`. -/
  pre : Expr
  /-- How the frame was requested: an `explicit` frame from a `frames` clause, or the `implicit` spec
  precondition to infer it from. -/
  hint : FrameInferenceHint
  /-- Declaration name of the `@[spec]` theorem being applied, `none` for a local or syntactic spec.
  A procedure can key a footprint off it, e.g. through an attribute keyed by spec name. -/
  spec? : Option Name
  /-- The residual precondition the program runs against once `frame` is framed off: in the split VC
  `pre ⊑ op frame residualPre`, the complement of `frame` in `pre`. A solver-owned synthetic-opaque
  metavariable the procedure must not assign; the solver fills it once the frame rule fixes it. -/
  residualPre : Expr

/-- The split VC proposition `pre ⊑ (op frame footprint) s⃗`: the frame operator applied to `frame`
and `footprint`, then to the excess state arguments, entailed by `pre` in the goal's order. -/
public def VCGen.FrameInferenceInfo.mkSplitVC (i : FrameInferenceInfo) (frame footprint : Expr) :
    SymM Expr := do
  let rhs ← mkAppNS (← mkAppNS i.op #[frame, footprint]) i.excessArgs
  mkAppNS i.le #[i.pre, rhs]

/-- A `FrameSplit` framing `frame` whose split VC `pre ⊑ (op frame residualPre) s⃗` is deferred as a
fresh subgoal for the built-in lattice (meet) decomposition to split. -/
public def VCGen.FrameSplit.withDeferredSplitVC (i : FrameInferenceInfo) (frame : Expr) :
    SymM FrameSplit := do
  let m ← mkFreshExprSyntheticOpaqueMVar (← i.mkSplitVC frame i.residualPre)
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

/-- A frame inference procedure: from a `FrameInferenceInfo` (whose `hint` says whether the frame is
`explicit` or must be inferred from the spec precondition), optionally produce a `FrameSplit`; `none`
leaves the spec to apply directly.

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
  /-- Builds the frame operator (head constant `opHead`) applied to the goal's assertion type. -/
  mkOpAppM : VCGen.WPApp → MetaM Expr
  /-- The resource type `R` of the operator `op : R → Pred → Pred`, i.e. the domain of `mkOpAppM`'s
  result. Provided directly so `vcgen` reads it without building the operator, which it does only when
  a frame actually applies. -/
  resourceTy : VCGen.WPApp → MetaM Expr
  /-- Head constant of the frame operator, locating the split VC in the frame rule. -/
  opHead : Name
  /-- The frame inference metaprogram. -/
  proc : VCGen.FrameInferenceProc

/-- The registered frame inference procedures, indexed by the program monad's head constant
(selected per node in `solve`). -/
public structure VCGen.FrameProcs where
  byProg : Std.HashMap Name VCGen.FrameProc := {}

public instance : Inhabited VCGen.FrameProcs := ⟨{}⟩

public def VCGen.FrameProcs.insert (s : FrameProcs) (fp : FrameProc) : FrameProcs :=
  { byProg := s.byProg.insert fp.prog fp }

/-- Default meet frame procedure: frame the resource pinned by a `frames` clause, with the weakest
footprint. -/
public def VCGen.meetFrameInferenceProc : FrameInferenceProc := fun i => do
  match i.hint with
  | .explicit frame => return some (← FrameSplit.withDeferredSplitVC i frame)
  | .implicit _ => return none

/-- The default frame operator: lattice meet `pre ⊓ frame`, the Hoare frame every complete lattice carries.
Framed only through an explicit `frames` clause; used for a monad with no registered `@[frameproc]`. -/
public def VCGen.meetFrameProc : VCGen.FrameProc where
  prog := ``Lean.Order.meet
  mkOpAppM info := Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]
  resourceTy info := pure info.Pred
  opHead := ``Lean.Order.meet
  proc := meetFrameInferenceProc

end Lean.Elab.Tactic.Do.Internal
