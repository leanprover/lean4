/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.AIG.RefVecOperator
import Init.Grind

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

@[grind! .]
theorem mkEq_le_size (aig : AIG α) (input : aig.BinaryRefVec w) :
    aig.decls.size ≤ (mkEq aig input).aig.decls.size := by
  intros
  unfold mkEq
  grind

@[grind =]
theorem mkEq_decl_eq (aig : AIG α) (input : aig.BinaryRefVec w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (mkEq aig input).aig.decls.size) :
    (mkEq aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold mkEq
  grind

instance {w : Nat} : AIG.LawfulOperator α (AIG.BinaryRefVec · w) mkEq where
  le_size := mkEq_le_size
  decl_eq := mkEq_decl_eq

end BVPred

end Std.Tactic.BVDecide
