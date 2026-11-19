/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Init.System.IO
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
import Std.Data.HashMap.Basic


/-!
This module contains efficient evaluation for the reification data types of `bv_decide`, used for
evaluating counterexamples during CEGAR.
-/

namespace Std.Tactic.BVDecide

namespace EfficientEval

structure Cache where
  exprMap : Std.DHashMap BVExpr.Cache.Key (fun k => BitVec k.w) := {}

abbrev EvalM (σ : Type) := ReaderT (Nat → BVExpr.PackedBitVec) StateRefT Cache (ST σ)

@[inline]
def EvalM.run (assign : Nat → BVExpr.PackedBitVec) (x : (σ : Type) → EvalM σ α) : α :=
  runST fun σ =>
    let x : EvalM σ α := x σ
    StateRefT'.run' (ReaderT.run x assign) {}

partial def BVExpr.evalEfficientM (expr : BVExpr w) : EvalM σ (BitVec w) := do
  let key := ⟨w, expr⟩
  if let some res := (← get).exprMap.get? key then
    return res
  else
    let res ← go expr
    modify fun s => { s with exprMap := s.exprMap.insert key res }
    return res
where
  go {w : Nat} : BVExpr w → EvalM σ (BitVec w)
    | .var idx => do
      let packedBv := (← read) idx
      /-
      This formulation improves performance, as in a well formed expression the condition always holds
      so there is no need for the more involved `BitVec.truncate` logic.
      -/
      if h : packedBv.w = w then
        return h ▸ packedBv.bv
      else
        return packedBv.bv.truncate w
    | .const val => return val
    | .extract start len expr => return BitVec.extractLsb' start len (← evalEfficientM expr)
    | .bin lhs op rhs => return op.eval (← evalEfficientM lhs) (← evalEfficientM rhs)
    | .un op operand => return op.eval (← evalEfficientM operand)
    | .append lhs rhs h => return h ▸ ((← evalEfficientM lhs) ++ (← evalEfficientM rhs))
    | .replicate n expr h => return h ▸ (BitVec.replicate n (← evalEfficientM expr))
    | .shiftLeft lhs rhs => return (← evalEfficientM lhs) <<< (← evalEfficientM rhs)
    | .shiftRight lhs rhs => return (← evalEfficientM lhs) >>> (← evalEfficientM rhs)
    | .arithShiftRight lhs rhs => return BitVec.sshiftRight' (← evalEfficientM lhs) (← evalEfficientM rhs)

partial def BVPred.evalEfficientM (expr : BVPred) : EvalM σ Bool := do
  match expr with
  | .bin lhs op rhs => return op.eval (← BVExpr.evalEfficientM lhs) (← BVExpr.evalEfficientM rhs)
  | .getLsbD expr idx => return (← BVExpr.evalEfficientM expr).getLsbD idx

partial def BVLogicalExpr.evalEfficientM (expr : BVLogicalExpr) : EvalM σ Bool := do
  match expr with
  | .literal l => BVPred.evalEfficientM l
  | .const b => return b
  | .not x => return !(← evalEfficientM x)
  | .gate g x y => return g.eval (← evalEfficientM x) (← evalEfficientM y)
  | .ite d l r => bif (← evalEfficientM d) then evalEfficientM l else evalEfficientM r

public def BVExpr.evalEfficient (assign : Nat → BVExpr.PackedBitVec) (expr : BVExpr w) :
    BitVec w :=
  EvalM.run assign (fun σ => BVExpr.evalEfficientM (σ := σ) expr)

public def BVPred.evalEfficient (assign : Nat → BVExpr.PackedBitVec) (expr : BVPred) : Bool :=
  EvalM.run assign (fun σ => BVPred.evalEfficientM (σ := σ) expr)

public def BVLogicalExpr.evalEfficient (assign : Nat → BVExpr.PackedBitVec)
    (expr : BVLogicalExpr) : Bool :=
  EvalM.run assign (fun σ => BVLogicalExpr.evalEfficientM (σ := σ) expr)

end EfficientEval

end Std.Tactic.BVDecide
