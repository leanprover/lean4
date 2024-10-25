/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.CachedGatesLemmas
import Std.Sat.AIG.LawfulVecOperator
import Std.Sat.AIG.RefVecOperator

/-!
This module contains the implementation of a bitblaster for `BitVec` equality.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVPred

variable [Hashable α] [DecidableEq α]

def mkEq (aig : AIG α) (pair : AIG.BinaryRefVec aig w) : AIG.Entrypoint α :=
  let res := AIG.RefVec.zip aig ⟨pair, AIG.mkBEqCached⟩
  let aig := res.aig
  let bits := res.vec
  AIG.RefVec.fold aig (.mkAnd bits)

instance {w : Nat} : AIG.LawfulOperator α (AIG.BinaryRefVec · w) mkEq where
  le_size := by
    intros
    unfold mkEq
    dsimp only
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.RefVec.fold)
    apply AIG.LawfulVecOperator.le_size (f := AIG.RefVec.zip)
  decl_eq := by
    intros
    unfold mkEq
    dsimp only
    rw [AIG.LawfulOperator.decl_eq (f := AIG.RefVec.fold)]
    rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.zip)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.zip)
    assumption

end BVPred

end Std.Tactic.BVDecide
