/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Internal.Termination

public section

open Std.Iterators

structure RangeIterator where

instance : Iterator RangeIterator Id Nat := sorry

private def RangeIterator.instFinitenessRelation : FinitenessRelation RangeIterator Id where
  rel :=
    open Classical in
    InvImage WellFoundedRelation.rel (fun it => 0)
  wf := sorry
  subrelation {it it'} h := by
    simp_wf
    sorry
