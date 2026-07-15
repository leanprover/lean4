import Lean.Elab.Tactic.Basic
import Std.Tactic.BVDecide

/-! `replayConst` should be able to replay constants using additional axioms. -/

open Lean Lean.Meta Lean.Elab.Tactic in
elab "replay" ts:tacticSeq : tactic => do
  let initEnv ← getEnv
  evalTactic ts
  let finalState ← saveState
  setEnv $ ← initEnv.replayConsts initEnv finalState.term.meta.core.env

theorem test
    (x y : BitVec 128) (h : y = x) : x = y := by
  replay bv_decide
