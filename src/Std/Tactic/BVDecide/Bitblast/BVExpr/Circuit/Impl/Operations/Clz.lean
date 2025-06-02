/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Sat.AIG.LawfulVecOperator

/-!
This module contains the implementation of a bitblaster for `BitVec.clz`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

/--
  Count the number of leading zeroes downward from the 'n'th bit to the '0'th bit.
-/
-- def clzAux {w : Nat} (x : BitVec w) (n : Nat) : Nat :=
--   match n with
--   | 0 => if x.getLsbD 0 then 0 else 1
--   | n' + 1 =>
--     if x.getLsbD n then 0
--       else 1 + clzAux x n'


def blastClz (aig : AIG α) (target : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  let ⟨input, distance⟩ := target
  aig (.emptyWithCapacity w)
where
  go (aig : AIG α) (input : AIG.RefVec aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefVec aig curr) :
      AIG.RefVecEntry α w :=
  if hidx : curr < w then
    if hdist : (distance + curr) < w then
      let s := s.push (input.get (distance + curr) (by omega))
      go aig input distance (curr + 1) (by omega) s
    else
      let res := aig.mkConstCached false
      let aig := res.aig
      let zeroRef := res.ref
      have hfinal := AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
      let s := s.cast hfinal
      let input := input.cast hfinal
      let s := s.push zeroRef
      go aig input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    ⟨aig, hcurr ▸ s⟩
termination_by w - curr

-- def blastClz (aig : AIG α) (s : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
--   let clz := (1 : Nat)
--   let ⟨refs, hrefs⟩ := s
--   ⟨aig, ⟨sorry, by sorry⟩⟩

instance : AIG.LawfulVecOperator α AIG.RefVec blastClz where
  le_size := by simp [blastClz]; sorry
  decl_eq := by simp [blastClz]; sorry

end bitblast
end BVExpr

end Std.Tactic.BVDecide
