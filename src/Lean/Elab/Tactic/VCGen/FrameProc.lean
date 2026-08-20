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

/-! # Frame inference procedure protocol

This note describes the protocol between `vcgen`'s solver and a frame inference procedure, and the
metadata that is passed around.

The job of the frame inference procedure is to decide whether to frame the goal, and if so, how to
frame it, by assigning metavariables `?frame` and `?footprint` and producing the proofs supporting
that split.
`?frame` is the part of `P` that `prog` preserves. `?footprint` is the part of `P` that fits the
spec's precondition. `W` is the weakest footprint the rule leaves.

```
goal          : P ⊑ wp prog Q E s⃗
   │ frame rule, introducing ?frame
   ▼
split VC      : P ⊑ (op ?frame W) s⃗      side goal: Frames op prog ?frame
   where        W = wp prog (fun a => adj (op ?frame) (Q a)) E
   │ spec rule, at a target the frameproc named
   ▼
spec target   : ?footprint ⊑ W t⃗
   where
    pre VC    : ?footprint ⊑ specP
    post VCs  : ...
```

# Protocol

1. Solver. Look up the candidate specs for `prog` and take the highest priority one.
   A spec with a conjunctive precondition applies directly: no frameproc runs.
   Otherwise, look up the frameproc for the program type.
   The goal, the selected spec, and the matched `frames` clause, if any, go to the frameproc.
2. Frameproc, phase one. Answer `decline`, or answer `commit` and name `t⃗`, the state the spec runs
   at. The length of `t⃗` picks the rule.
3. Solver. On `decline`, apply the spec to the goal and hand back its subgoals.
4. Solver. On `commit`, apply the frame rule to a copy of the goal. This yields `?frame`, `W`, the
   split VC and the side goal.
5. Solver. Apply the spec at `?footprint ⊑ W t⃗`. On failure, drop the copy and try the next
   candidate.
6. Solver. Pass `?frame`, `?footprint`, `W`, `specP`, the pre VC and the proof of the spec target
   to the frameproc.
7. Frameproc, phase two. Choose `?frame`. Sometimes only `specP` says which.
8. Frameproc. Prove the split VC, composing the spec target's proof under `op`. It can leave
   `?frame` open, but never the split VC.
9. Frameproc. Discharge the pre VC when its own work proved it. Otherwise the solver forwards it.
10. Solver. Assign the goal from the copy and return the remaining goals.

# Requirements

11. The separation logic frameproc must assign the logical variables of `specP`. It matches
    `?l ↦ ?v` against the goal precondition, and that match fixes `?l` and `?v`.
12. The assignment of e.g., `?l` and `?v` requires domain knowledge and cannot easily be
    reconstructed by e.g., `rfl`. Thus, the assignment produced by the frameproc must persist.
13. `t⃗` cannot depend on `specP`. Only the solver produces `specP`, and it needs the length of `t⃗`
    first.
14. A frameproc that declines must be as fast as if there were no frameproc mechanism at all.
15. When the spec rule fails, the solver tries the next candidate. Backtracking after failure must
    be fast.
16. Emitted VCs are born with as few assigned metavariables as possible, so that sharing is kept.
17. The frameproc always discharges the split VC, so the spec target's proof is always used, and
    every emitted VC is a hole of the final proof. The meet frameproc proves its split VC with
    shared code that supports excess state arguments.
18. A pinned frame is consumed by the framing that lands, never by an attempt. A candidate that
    falls through must leave the `frames` clause for the next candidate.
-/

open Lean Meta Sym Sym.Internal

namespace Lean.Elab.Tactic.VCGen

/-- What a frameproc sees in phase one, in the order of the goal `pre ⊑ wp prog Q E s⃗`. -/
public structure FrameInferenceInfo where
  /-- The goal's precondition `P`. -/
  pre : Expr
  /-- The goal's entailment relation, with carrier and order instance applied. Apply it to two
  operands to state an entailment. -/
  le : Expr
  /-- The goal's `wp` application. Its `excessArgs` are the state arguments `s⃗`. -/
  unframedApp : WPApp
  /-- The frame a `frames` clause pinned at this call site, if any. -/
  providedFrame? : Option Expr
  /-- The name of the spec being applied, if it has one. Useful to key a footprint off. -/
  spec? : Option Name
  /-- Builds the frame operator `op : R → Pred → Pred`, hash-consed. -/
  mkOpApp : SymM Expr

/-- What the solver hands to phase two: the goal after framing, with the spec applied at the
footprint target `?footprint ⊑ W t⃗`. -/
public structure FrameGoal where
  /-- The schematic frame `?frame`. Assign it, or leave it open and it becomes a goal. -/
  frame : MVarId
  /-- The open footprint `?footprint`. Assign it to the part of `pre` that pays the spec. -/
  footprint : MVarId
  /-- The framed application `W t⃗`, where `W = wp prog (fun a => adj (op ?frame) (Q a)) E` and `t⃗`
  is the state named in phase one. `specProof` proves the entailment into it. -/
  framedApp : WPApp
  /-- The spec's precondition, with the spec's logical variables live: assignments made while
  matching against it persist. -/
  specPre : Expr
  /-- The VC `?footprint ⊑ specPre`. Discharge it when your own work proves it. Otherwise it
  becomes a goal. -/
  preVC : MVarId
  /-- The proof of the footprint target `?footprint ⊑ W t⃗`. -/
  specProof : Expr
  /-- Decompose an entailment goal `x ⊑ (op …) s⃗` through the lattice split registered for the
  operator head. `none` when no split is registered or the rule does not apply. -/
  splitLatticeOp? : MVarId → Grind.GrindM (Option (List MVarId))

/-- What phase two returns: a proof of the split VC `pre ⊑ (op ?frame W) s⃗`, and the goals the
frameproc itself created. Goals of the frame rule and of the spec need no forwarding. -/
public structure FrameSplit where
  /-- The split VC proof. Compose `FrameGoal.specProof` under the frame operator. -/
  splitVCProof : Expr
  /-- The goals the frameproc created, for example a guard it could not discharge. -/
  subgoals : List MVarId

/-- Phase one's answer. `decline` leaves the spec to apply without any frame. `commit` names `t⃗`,
the state the spec runs at, and continues in phase two once the solver applied the frame rule and
the spec; see `FrameGoal`. There is no way back after `commit`: when nothing needs framing, frame
the unit of the operator instead. -/
public inductive FrameDecision where
  | decline
  | commit (excessStates : Array Expr) (k : FrameGoal → Grind.GrindM FrameSplit)

/-- A frame inference procedure. Phase one sees the goal through `FrameInferenceInfo` and answers
a `FrameDecision`. The spec's precondition is only visible in phase two, after `commit`. -/
public abbrev FrameInferenceProc :=
  FrameInferenceInfo → Grind.GrindM FrameDecision

/-- A frame backward rule together with the positions of the schematic frame and the split VC in
the applied rule's goal list, fixed at rule construction. -/
public structure FrameBackwardRule where
  /-- The backward rule concluding `pre ⊑ wp prog Q E s⃗`. -/
  rule : Lean.Meta.Sym.BackwardRule
  /-- Position of the split VC `pre ⊑ (op frame W) s⃗`. -/
  splitVCIdx : Nat
  /-- Position of the schematic frame (of type `R`). -/
  frameIdx : Nat

/-- A frame inference procedure registered with `@[frameproc]`, together with its frame operator.
`vcgen` selects the one whose `prog` matches the goal program's monad. -/
public structure FrameProc where
  /-- Head constant of the program type (the monad) this procedure frames. -/
  prog : Name
  /-- Head constant of the frame operator, locating the split VC in the frame rule. -/
  opHead : Name
  /-- Builds the frame operator (head constant `opHead`) applied to the goal's assertion type. -/
  mkOpAppM : WPApp → MetaM Expr
  /-- The resource type `R` of the operator `op : R → Pred → Pred`. -/
  mkResourceTy : WPApp → MetaM Expr
  /-- The frame inference metaprogram. -/
  proc : FrameInferenceProc

/-- The registered frame inference procedures, indexed by the program monad's head constant. -/
public structure FrameProcs where
  byProg : Std.HashMap Name FrameProc := {}

public instance : Inhabited FrameProcs := ⟨{}⟩

public def FrameProcs.insert (s : FrameProcs) (fp : FrameProc) : FrameProcs :=
  { byProg := s.byProg.insert fp.prog fp }

/-- Commit to `frame`, take the whole precondition as the footprint, and discharge the split VC
with `FrameGoal.splitLatticeOp?`. Fits any frameproc whose operator has a registered lattice split,
for example the default meet frame. -/
public def FrameDecision.ofFrame (i : FrameInferenceInfo) (frame : Expr) : FrameDecision :=
  .commit i.unframedApp.excessArgs fun goal => do
    let frame ← shareCommon frame
    goal.frame.assign frame
    goal.footprint.assign i.pre
    let rhs ← mkAppNS (← mkAppNS (← i.mkOpApp) #[frame, goal.framedApp.wp]) i.unframedApp.excessArgs
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS i.le #[i.pre, rhs])
    let some gs ← goal.splitLatticeOp? m.mvarId!
      | throwError "frameproc: no lattice split applies to{indentExpr (← m.mvarId!.getType)}"
    -- The split leaves `pre ⊑ frame s⃗` and `pre ⊑ W s⃗`; `specProof` proves the second.
    let subgoals ← gs.filterM fun g => do
      if (isWPApp? (← g.getType).appArg!).isSome then g.assign goal.specProof; return false
      else return true
    return { splitVCProof := m, subgoals }

/-- Default frame inference procedure: frame the resource a `frames` clause pinned, and decline
otherwise. -/
public def defaultFrameInferenceProc : FrameInferenceProc := fun i => do
  let some frame := i.providedFrame? | return .decline
  return .ofFrame i frame

/-- The lattice meet operator over the goal's assertion type. -/
private def meetOp (info : WPApp) : MetaM Expr :=
  Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]

/-- The default frame operator: lattice meet `pre ⊓ frame`, the Hoare frame every complete lattice
carries. Used for a monad with no registered `@[frameproc]`. -/
public def meetFrameProc : FrameProc where
  prog := ``Lean.Order.meet
  mkOpAppM := meetOp
  mkResourceTy info := pure info.Pred
  opHead := ``Lean.Order.meet
  proc := defaultFrameInferenceProc

end Lean.Elab.Tactic.VCGen
