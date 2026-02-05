/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Lean.Meta.Basic
import Lean.Meta.InferType
import Init.Omega

open Lean Meta

/-!
This module provides builder for efficient `Nat → …` functions based on binary decision trees.
-/

/--
Builds an expression of type `Nat → $type` that returns the `es[i]`, using binary search.
The array must be non-empty.
-/
public def mkNatLookupTable (i : Expr) (type : Expr) (es : Array Expr) : MetaM Expr := do
  if h : es.size = 0 then
    panic! "mkNatLookupTable: expected non-empty array"
  else
    let u ← getLevel type
    let rec go (start stop : Nat) (hstart : start < stop := by omega) (hstop : stop ≤ es.size := by omega) : MetaM Expr := do
      if h : start + 1 = stop then
        return es[start]
      else
        let mid := (start + stop) / 2
        let low ← go start mid
        let high ← go mid stop
        return mkApp4 (mkConst ``cond [u]) type (mkApp2 (mkConst ``Nat.ble) i (mkRawNatLit (mid-1))) low high
    go 0 es.size
