/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.AIG.RefVecOperator

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec` equality.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVPred

variable [Hashable α] [DecidableEq α]

def mkEq (aig : AIG α) (pair : AIG.BinaryRefVec aig w) : AIG.Entrypoint α :=
  let res := AIG.RefVec.zip aig pair AIG.mkBEqCached
  let aig := res.aig
  let bits := res.vec
  AIG.RefVec.fold aig bits AIG.mkAndCached

instance {w : Nat} : AIG.LawfulOperator α (AIG.BinaryRefVec · w) mkEq where
  le_size := by
    intros
    unfold mkEq
    dsimp only
    apply AIG.RefVec.fold_le_size_of_le_aig_size
    apply AIG.RefVec.zip_le_size
  decl_eq := by
    intros
    unfold mkEq
    dsimp only
    rw [AIG.RefVec.fold_decl_eq]
    rw [AIG.RefVec.zip_decl_eq]
    apply AIG.RefVec.zip_lt_size_of_lt_aig_size
    assumption

end BVPred

end Std.Tactic.BVDecide
