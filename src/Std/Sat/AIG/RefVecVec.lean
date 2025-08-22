/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini
-/
module

prelude
public import Std.Sat.AIG.LawfulOperator
public import Std.Sat.AIG.CachedGatesLemmas
public import Init.Data.Vector.Lemmas

@[expose] public section

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α] {aig : AIG α}

namespace RefVec


/-- A vector of `AIG.RefVec aig w` of size n. -/
structure RefVecVec {α : Type} [DecidableEq α] [Hashable α] [DecidableEq α] (aig : AIG α) (w : Nat) (n : Nat) where
  vec : Vector (AIG.RefVec aig w) n

/-- A vector of `AIG.RefVec aig w` (vec) pointing to the same AIG (aig)-/
structure RefVecEntryVec (α : Type) [DecidableEq α] [Hashable α] [DecidableEq α] (w : Nat) (n : Nat) where
  aig : AIG α
  vec : RefVecVec aig w n

/-- Casting `RefVecVec` -/
def RefVecVec.cast {aig1 aig2 : AIG α} (s : RefVecVec aig1 lenWords len) (h : aig1.decls.size ≤ aig2.decls.size) :
    RefVecVec aig2 lenWords len :=
  let vec' := s.vec.map fun rv => AIG.RefVec.cast rv h
  RefVecVec.mk vec'

/-- When inserting a new element `elem` to vec we need to cast all the AIGs of its elements to the new element's AIG (elem.aig)-/
def RefVecVec.set {aigOld aigNew: AIG α} {n w : Nat} (idx : Nat) (vec : RefVecVec aigOld w n) (elem : AIG.RefVec aigNew w) (haig: aigOld.decls.size ≤ aigNew.decls.size) (proof : idx < n ):
  RefVecVec aigNew w n :=
  let vec' : Vector (AIG.RefVec aigNew w) n := vec.vec.map fun refVec => refVec.cast haig
  {vec := vec'.set idx elem proof}
