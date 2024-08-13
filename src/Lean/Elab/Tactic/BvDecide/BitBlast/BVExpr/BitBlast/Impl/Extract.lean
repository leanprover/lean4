/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr.Basic
import Std.Sat.AIG.LawfulVecOperator

namespace Lean.Elab.Tactic.BvDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

structure ExtractTarget (aig : AIG α) (newWidth : Nat) where
  {w : Nat}
  vec : AIG.RefVec aig w
  hi : Nat
  lo : Nat
  hnew : newWidth = hi - lo + 1

def blastExtract (aig : AIG α) (target : ExtractTarget aig newWidth) :
    AIG.RefVecEntry α newWidth :=
  let ⟨input, hi, lo, hnew⟩ := target
  let res := aig.mkConstCached false
  let aig := res.aig
  let falseRef := res.ref
  let input := input.cast <| AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
  if h : lo ≤ hi then
    ⟨aig, go input lo falseRef 0 (by omega) .empty⟩
  else
    have : 1 = newWidth  := by omega
    let base := AIG.RefVec.empty
    let base := base.push (input.getD lo falseRef)
    ⟨aig, this ▸ base⟩
where
  go {aig : AIG α} {w : Nat} (input : AIG.RefVec aig w) (lo : Nat) (falseRef : AIG.Ref aig)
      (curr : Nat) (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
      AIG.RefVec aig newWidth :=
  if h : curr < newWidth then
    let nextRef := input.getD (lo + curr) falseRef
    let s := s.push nextRef
    go input lo falseRef (curr + 1) (by omega) s
  else
    have : curr = newWidth := by omega
    this ▸ s
termination_by newWidth - curr

instance : AIG.LawfulVecOperator α ExtractTarget blastExtract where
  le_size := by
    intros
    unfold blastExtract
    dsimp only
    split
    all_goals
      simp only
      apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  decl_eq := by
    intros
    unfold blastExtract
    dsimp only
    split
    all_goals
      simp only
      rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]

end bitblast
end BVExpr

end Lean.Elab.Tactic.BvDecide
