/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.CommSolver
public import Init.GrindInstances.Ring.Int
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.LemmasAux
public import Init.Data.Int.Linear
import Init.Omega
public section

/-!
# `Int` certificates for the `Sym.Arith` normalizer

Over `Int`, a linear relation `k * q + c = 0` with `k > 0` forces `k ∣ c`, and
`k * q + c ≤ 0 ↔ q + ⌈c / k⌉ ≤ 0`. These theorems let the normalizer divide the coefficients
of an `Int` relation by their gcd, close an equation whose constant is not divisible by the
gcd, tighten an inequality, and normalize a divisibility constraint `k ∣ e` by the gcd of `k`
and the coefficients of `e`, as `simp +arith` does with `Int.Linear`. The polynomial `q` and
the constant `c` are computed by the normalizer; the kernel checks `p = k * q + c` by
evaluation (`split_cert`).
-/

namespace Lean.Grind.CommRing
open Int.Internal.Linear (cdiv)

/-- `p = k * q + c` with `k > 0`. -/
@[expose] noncomputable def split_cert (p q : Poly) (k c : Int) : Bool :=
  Int.blt' 0 k |>.and (p.beq' ((q.mulConst_k k).addConst_k c))

theorem denote_of_split_cert (ctx : Context Int) {p q : Poly} {k c : Int}
    (h : split_cert p q k c) : 0 < k ∧ p.denote ctx = k * q.denote ctx + c := by
  simp [split_cert] at h
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨h₁, ?_⟩
  rw [h₂, Poly.addConst_k_eq_addConst, Poly.denote_addConst, Poly.denote_mulConst]
  simp

@[expose] noncomputable def eq_div_cert (lhs rhs lhs' rhs' : Expr) (k : Int) : Bool :=
  !Int.beq' k 0 |>.and ((lhs.sub rhs).toPoly_k.beq' ((lhs'.sub rhs').toPoly_k.mulConst_k k))

theorem eq_norm_div_expr (ctx : Context Int) (lhs rhs lhs' rhs' : Expr) (k : Int)
    : eq_div_cert lhs rhs lhs' rhs' k → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  simp [eq_div_cert]
  intro hk h
  replace h := congrArg (Poly.denote ctx) h
  simp [Expr.denote_toPoly, Poly.denote_mulConst] at h
  replace h : lhs.denote ctx - rhs.denote ctx = k * (lhs'.denote ctx - rhs'.denote ctx) := h
  rw [← Int.sub_eq_zero, ← Int.sub_eq_zero (a := lhs'.denote ctx), h, Int.mul_eq_zero]
  simp [hk]

@[expose] noncomputable def eq_unsat_cert (lhs rhs : Expr) (q : Poly) (k c : Int) : Bool :=
  split_cert (lhs.sub rhs).toPoly_k q k c |>.and (!Int.beq' (c % k) 0)

theorem eq_norm_unsat_expr (ctx : Context Int) (lhs rhs : Expr) (q : Poly) (k c : Int)
    : eq_unsat_cert lhs rhs q k c → (lhs.denote ctx = rhs.denote ctx) = False := by
  simp only [eq_unsat_cert, Bool.and_eq_true]
  intro ⟨h, hc⟩
  simp at hc
  have ⟨hk, h⟩ := denote_of_split_cert ctx h
  simp [Expr.denote_toPoly] at h
  replace h : lhs.denote ctx - rhs.denote ctx = k * q.denote ctx + c := h
  apply eq_false
  intro heq
  rw [heq, Int.sub_self] at h
  have : c = -(k * q.denote ctx) := by omega
  have : c % k = 0 := by
    rw [this]; exact Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr (Int.dvd_mul_right k _))
  exact hc this

@[expose] noncomputable def le_tight_cert (lhs rhs lhs' rhs' : Expr) (q : Poly) (k c : Int) : Bool :=
  split_cert (lhs.sub rhs).toPoly_k q k c |>.and ((lhs'.sub rhs').toPoly_k.beq' (q.addConst_k (cdiv c k)))

theorem le_norm_tight_expr (ctx : Context Int) (lhs rhs lhs' rhs' : Expr) (q : Poly) (k c : Int)
    : le_tight_cert lhs rhs lhs' rhs' q k c → (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  simp only [le_tight_cert, Bool.and_eq_true, Poly.beq'_eq]
  intro ⟨h, h'⟩
  have ⟨hk, h⟩ := denote_of_split_cert ctx h
  replace h' := congrArg (Poly.denote ctx) h'
  rw [Poly.addConst_k_eq_addConst, Poly.denote_addConst] at h'
  simp [Expr.denote_toPoly] at h h'
  replace h : lhs.denote ctx - rhs.denote ctx = k * q.denote ctx + c := h
  replace h' : lhs'.denote ctx - rhs'.denote ctx = q.denote ctx + cdiv c k := h'
  apply propext
  have e₁ : lhs.denote ctx ≤ rhs.denote ctx ↔ k * q.denote ctx + c ≤ 0 := by omega
  have e₂ : lhs'.denote ctx ≤ rhs'.denote ctx ↔ q.denote ctx + cdiv c k ≤ 0 := by omega
  rw [e₁, e₂]
  unfold cdiv
  constructor
  · intro hle
    have h₁ : q.denote ctx * k ≤ -c := by rw [Int.mul_comm]; omega
    have h₂ := (Int.le_ediv_iff_mul_le hk).mpr h₁
    omega
  · intro hle
    have h₁ : q.denote ctx ≤ (-c) / k := by omega
    have h₂ := (Int.le_ediv_iff_mul_le hk).mp h₁
    rw [Int.mul_comm] at h₂
    omega

@[expose] noncomputable def dvd_cert (k : Int) (e e' : Expr) (k' : Int) (q : Poly) (g c : Int) : Bool :=
  split_cert e.toPoly_k q g c |>.and (Int.beq' k (k' * g)) |>.and (Int.beq' (c % g) 0)
    |>.and (e'.toPoly_k.beq' (q.addConst_k (c / g)))

theorem dvd_norm_expr (ctx : Context Int) (k : Int) (e e' : Expr) (k' : Int) (q : Poly) (g c : Int)
    : dvd_cert k e e' k' q g c → (k ∣ e.denote ctx) = (k' ∣ e'.denote ctx) := by
  simp only [dvd_cert, Bool.and_eq_true, Poly.beq'_eq]
  intro ⟨⟨⟨h, hk⟩, hc⟩, h'⟩
  simp at hk hc
  have ⟨hg, h⟩ := denote_of_split_cert ctx h
  replace h' := congrArg (Poly.denote ctx) h'
  rw [Poly.addConst_k_eq_addConst, Poly.denote_addConst] at h'
  simp [Expr.denote_toPoly] at h h'
  have hcg : g * (c / g) = c := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hc)
  have : g * q.denote ctx + c = g * (q.denote ctx + c / g) := by rw [Int.mul_add, hcg]
  apply propext
  rw [h, h', hk, this, Int.mul_comm k' g]
  exact Int.mul_dvd_mul_iff_left (Int.ne_of_gt hg)

@[expose] noncomputable def dvd_unsat_cert (k : Int) (e : Expr) (q : Poly) (g c : Int) : Bool :=
  split_cert e.toPoly_k q g c |>.and (Int.beq' (k % g) 0) |>.and (!Int.beq' (c % g) 0)

theorem dvd_norm_unsat_expr (ctx : Context Int) (k : Int) (e : Expr) (q : Poly) (g c : Int)
    : dvd_unsat_cert k e q g c → (k ∣ e.denote ctx) = False := by
  simp only [dvd_unsat_cert, Bool.and_eq_true]
  intro ⟨⟨h, hk⟩, hc⟩
  simp at hk hc
  have ⟨hg, h⟩ := denote_of_split_cert ctx h
  simp [Expr.denote_toPoly] at h
  apply eq_false
  intro hd
  rw [h] at hd
  have h₁ : g ∣ g * q.denote ctx + c := Int.dvd_trans (Int.dvd_of_emod_eq_zero hk) hd
  have h₂ : g ∣ c := (Int.dvd_add_right (Int.dvd_mul_right g _)).mp h₁
  exact hc (Int.emod_eq_zero_of_dvd h₂)

end Lean.Grind.CommRing
