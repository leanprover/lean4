/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Offset
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind.Arith

/-!
Helper functions for constructing proof terms in the arithmetic procedures.
-/

namespace Offset

/-- Returns a proof for `true = true` -/
def rfl_true : Expr := mkConst ``Grind.rfl_true

open Lean.Grind in
/--
Assume `pi₁` is `{ w := u, k := k₁, proof := p₁ }` and `pi₂` is `{ w := w, k := k₂, proof := p₂ }`
`p₁` is the proof for edge `u -(k₁) → w` and `p₂` the proof for edge `w -(k₂)-> v`.
Then, this function returns a proof for edge `u -(k₁+k₂) -> v`.
-/
def mkTrans (nodes : PArray Expr) (pi₁ : ProofInfo) (pi₂ : ProofInfo) (v : NodeId) : ProofInfo :=
  let { w := u, k := k₁, proof := p₁ } := pi₁
  let { w, k := k₂, proof := p₂ } := pi₂
  let u := nodes[u]!
  let w := nodes[w]!
  let v := nodes[v]!
  let p := if k₁ == 0 then
    if k₂ == 0 then
      -- u ≤ w, w ≤ v
      mkApp5 (mkConst ``Nat.le_trans) u w v p₁ p₂
    else if k₂ > 0 then
      -- u ≤ v, w ≤ v + k₂
      mkApp6 (mkConst ``Nat.le_ro) u w v (toExpr k₂.toNat) p₁ p₂
    else
      let k₂ := - k₂
      -- u ≤ w, w + k₂ ≤ v
      mkApp6 (mkConst ``Nat.le_lo) u w v (toExpr k₂.toNat) p₁ p₂
  else if k₁ < 0 then
    let k₁ := -k₁
    if k₂ == 0 then
      mkApp6 (mkConst ``Nat.lo_le) u w v (toExpr k₁.toNat) p₁ p₂
    else if k₂ < 0 then
      let k₂ := -k₂
      mkApp7 (mkConst ``Nat.lo_lo) u w v (toExpr k₁.toNat) (toExpr k₂.toNat) p₁ p₂
    else
      let ke₁ := toExpr k₁.toNat
      let ke₂ := toExpr k₂.toNat
      if k₁ > k₂ then
        mkApp8 (mkConst ``Nat.lo_ro_1) u w v ke₁ ke₂ rfl_true p₁ p₂
      else
        mkApp7 (mkConst ``Nat.lo_ro_2) u w v ke₁ ke₂ p₁ p₂
  else
    let ke₁ := toExpr k₁.toNat
    if k₂ == 0 then
      mkApp6 (mkConst ``Nat.ro_le) u w v ke₁ p₁ p₂
    else if k₂ < 0 then
      let k₂  := -k₂
      let ke₂ := toExpr k₂.toNat
       if k₂ > k₁ then
         mkApp8 (mkConst ``Nat.ro_lo_2) u w v ke₁ ke₂ rfl_true p₁ p₂
       else
         mkApp7 (mkConst ``Nat.ro_lo_1) u w v ke₁ ke₂ p₁ p₂
    else
      let ke₂ := toExpr k₂.toNat
      mkApp7 (mkConst ``Nat.ro_ro) u w v ke₁ ke₂ p₁ p₂
  { w := pi₁.w, k := k₁+k₂, proof := p }

open Lean.Grind in
def mkOfNegEqFalse (nodes : PArray Expr) (c : Cnstr NodeId) (h : Expr) : Expr :=
  let u := nodes[c.u]!
  let v := nodes[c.v]!
  if c.k == 0 then
    mkApp3 (mkConst ``Nat.of_le_eq_false) u v h
  else if c.k == -1 && c.le then
    mkApp3 (mkConst ``Nat.of_lo_eq_false_1) u v h
  else if c.k < 0 then
    mkApp4 (mkConst ``Nat.of_lo_eq_false) u v (toExpr (-c.k).toNat) h
  else
    mkApp4 (mkConst ``Nat.of_ro_eq_false) u v (toExpr c.k.toNat) h

/--
Returns a proof of `False` using a negative cycle composed of
- `u --(kuv)--> v` with proof `huv`
- `v --(kvu)--> u` with proof `hvu`
-/
def mkUnsatProof (u v : Expr) (kuv : Int) (huv : Expr) (kvu : Int) (hvu : Expr) : Expr :=
  if kuv == 0 then
    assert! kvu < 0
    mkApp6 (mkConst ``Grind.Nat.unsat_le_lo) u v (toExpr (-kvu).toNat) rfl_true huv hvu
  else if kvu == 0 then
    mkApp6 (mkConst ``Grind.Nat.unsat_le_lo) v u (toExpr (-kuv).toNat) rfl_true hvu huv
  else if kuv < 0 then
    if kvu > 0 then
      mkApp7 (mkConst ``Grind.Nat.unsat_lo_ro) u v (toExpr (-kuv).toNat) (toExpr kvu.toNat) rfl_true huv hvu
    else
      assert! kvu < 0
      mkApp7 (mkConst ``Grind.Nat.unsat_lo_lo) u v (toExpr (-kuv).toNat) (toExpr (-kvu).toNat) rfl_true huv hvu
  else
    assert! kuv > 0 && kvu < 0
    mkApp7 (mkConst ``Grind.Nat.unsat_lo_ro) v u (toExpr (-kvu).toNat) (toExpr kuv.toNat) rfl_true hvu huv

end Offset

end Lean.Meta.Grind.Arith
