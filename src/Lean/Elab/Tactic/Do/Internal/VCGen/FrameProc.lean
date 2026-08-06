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
public import Lean.Meta.Tactic.Grind.Types
import Std.Internal.Do.Order.Basic
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

namespace Lean.Elab.Tactic.Do.Internal

/-- The subgoals of a committed frame rule and spec rule application
(`FrameInferenceInfo.commit`). -/
public structure VCGen.FrameGoals where
  /-- The schematic frame `?F : R`. The procedure assigns it before returning. -/
  F : Expr
  /-- The split VC `pre ⊑ (op ?F specPre) s⃗`. The spec's parameter metavariables sit in `specPre`,
  so cancelling atoms against it pins them. When no spec rule applied, the second operand is the
  weakest footprint `W = wp prog (fun a => upperAdjoint (op ?F) (Q a)) E` instead. -/
  splitVC : MVarId
  /-- The frame condition `WP.Frames op prog ?F`. -/
  frames : MVarId
  /-- The spec rule's remaining subgoals: parameters and side conditions. -/
  specGoals : List MVarId

/-- The inputs to a `FrameInferenceProc`: the goal, how the frame was requested, and the spec being
applied. Extends the program's `wp` metadata (`WPApp`), so `Pred`, `excessArgs`, etc. are available
directly. -/
public structure VCGen.FrameInferenceInfo extends VCGen.WPApp where
  /-- The entailment goal `pre ⊑ wp …` the frame rule or spec applies to. -/
  goal : MVarId
  /-- The frame pinned by a matching `frames` clause, or `none` to infer the frame, e.g. from the
  precondition or from `peekSpecPre`. -/
  providedFrame? : Option Expr
  /-- Declaration name of the `@[spec]` theorem being applied, `none` for a local or syntactic spec.
  A procedure can key a footprint off it, e.g. through an attribute keyed by spec name. -/
  spec? : Option Name
  /-- The backward rule of the `@[spec]` theorem being applied. -/
  specRule : Lean.Meta.Sym.BackwardRule
  /-- Builds the frame operator `op : R → Pred → Pred`, hash-consed; the selected procedure's
  `FrameProc.mkOpAppM`. -/
  mkOpApp : SymM Expr
  /-- Commits the goal to the frame rule: applies it (assigning `goal`), resolves its residual
  premise by applying `specRule` where it fits (else fixes the weakest footprint), and returns the
  live subgoals. The point of no return: after this call the procedure must assign the frame and
  return; the solver collects the unassigned subgoals. -/
  commit : Grind.GrindM VCGen.FrameGoals

/-- The goal's entailment relation `PartialOrder.rel α inst` (carrier and order instance applied);
apply it to two operands to build an entailment in the goal's order. -/
public def VCGen.FrameInferenceInfo.le (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).stripArgsN 2

/-- What holds going in: the left-hand side of the goal entailment `pre ⊑ wp …`. -/
public def VCGen.FrameInferenceInfo.pre (i : FrameInferenceInfo) : SymM Expr :=
  return (← i.goal.getType).appFn!.appArg!

/-- The spec precondition instantiated at the call site, read off a `Pattern.match?` of the spec
rule's conclusion against the goal: parameters the conclusion does not determine come back as fresh
metavariables. Assignments against the result are dead; it informs the decision to `commit`, and the
procedure re-establishes any pairing on the live `splitVC` afterwards. `none` when the rule does not
match the goal or has no precondition VC. -/
public def VCGen.FrameInferenceInfo.peekSpecPre (i : FrameInferenceInfo) : SymM (Option Expr) := do
  let some res ← i.specRule.pattern.match? (← i.goal.getType) | return none
  let p := i.specRule.pattern
  for j in i.specRule.resultPos do
    let ty := p.varTypes[j]!.instantiateLevelParams p.levelParams res.us
      |>.instantiateRevRange 0 j res.args
    let_expr Lean.Order.PartialOrder.rel _ _ _ specPre := ty | continue
    return some (← shareCommon specPre)
  return none

/-- A frame inference procedure: from a `FrameInferenceInfo` (whose `providedFrame?` carries the
frame of a matching `frames` clause, if any), decide whether to frame. Framing means calling
`i.commit`, assigning the returned schematic frame, and discharging as much of the split VC as the
procedure can; the returned list carries any subgoals the procedure created doing so. Returning
without committing applies the spec unframed. -/
public abbrev VCGen.FrameInferenceProc :=
  VCGen.FrameInferenceInfo → Grind.GrindM (List MVarId)

/-- The procedure framing `frame` with the whole split VC left as a subgoal for the built-in lattice
decomposition: commit, assign the schematic frame, discharge nothing. -/
public def VCGen.FrameInferenceProc.ofFrame?
    (f : VCGen.FrameInferenceInfo → Grind.GrindM (Option Expr)) : VCGen.FrameInferenceProc :=
  fun i => do
    let some frame ← f i | return []
    let goals ← i.commit
    goals.F.mvarId!.assign (← shareCommon frame)
    return []

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
  /-- Head constant of the frame operator, locating the split VC among the frame rule's subgoals. -/
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
a `frames` clause, with the whole split VC deferred. -/
public def VCGen.defaultFrameInferenceProc : FrameInferenceProc :=
  .ofFrame? fun i => pure i.providedFrame?

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
  proc := defaultFrameInferenceProc

end Lean.Elab.Tactic.Do.Internal
