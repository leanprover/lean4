/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Sat.AIG.CachedGatesLemmas
import Std.Sat.AIG.LawfulVecOperator

/-!
This module contains the implementation of a bitblaster for `BitVec` constants.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastConst (aig : AIG α) (val : BitVec w) : AIG.RefVecEntry α w :=
  go aig val 0 .empty (by omega)
where
  go (aig : AIG α) (val : BitVec w) (curr : Nat) (s : AIG.RefVec aig curr) (hcurr : curr ≤ w) :
      AIG.RefVecEntry α w :=
    if hcurr : curr < w then
      let res := aig.mkConstCached (val.getLsbD curr)
      let aig := res.aig
      let bitRef := res.ref
      let s := s.cast <| AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
      let s := s.push bitRef
      go aig val (curr + 1) s (by omega)
    else
      have hcurr : curr = w := by omega
      ⟨aig, hcurr ▸ s⟩
  termination_by w - curr

theorem blastConst.go_le_size {aig : AIG α} (curr : Nat) (s : AIG.RefVec aig curr) (val : BitVec w)
    (hcurr : curr ≤ w) :
    aig.decls.size ≤ (go aig val curr s hcurr).aig.decls.size := by
  unfold go
  split
  · dsimp only
    refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulOperator.le_size
  · simp
termination_by w - curr

theorem blastConst.go_decl_eq {aig : AIG α} (i : Nat) (s : AIG.RefVec aig i) (val : BitVec w)
    (hi : i ≤ w) :
    ∀ (curr : Nat) (h1) (h2),
        (go aig val i s hi).aig.decls[curr]'h2 = aig.decls[curr]'h1 := by
  generalize hgo : go aig val i s hi = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    rw [← hgo]
    intro curr h1 h2
    rw [blastConst.go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
    assumption
  · dsimp only at hgo
    rw [← hgo]
    intros
    simp
termination_by w - i

instance : AIG.LawfulVecOperator α (fun _ w => BitVec w) blastConst where
  le_size := by
    intros
    unfold blastConst
    apply blastConst.go_le_size
  decl_eq := by
    intros
    unfold blastConst
    apply blastConst.go_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
