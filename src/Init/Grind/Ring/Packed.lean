/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.CommSolver
public import Init.Grind.Ring.CommSemiringAdapter
import Init.Omega
import Init.Grind.Ordered.Order
import Init.WFTactics
import Init.ByCases
import Init.Data.List.Lemmas
import Init.Data.Nat.Lemmas

@[expose] public section

namespace Lean.Grind.CommRing
/-!
Polynomials with packed monomials, for kernel-checked normalization in commutative rings.

The monomial `x₀^k₀ * ... * xₙ^kₙ` is packed as the natural number `k₀ + k₁ * B + ... + kₙ * B^n`
for a base `B` larger than every degree, so multiplying monomials adds their codes and comparing
them compares numbers, operations the kernel performs on literals directly. Each term also stores
its degree, and terms are sorted by decreasing degree and then by increasing code, which is the
order `Mon.grevlex` of `Poly`.
-/

open Std
open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg
open CommSemiring

attribute [local instance] Semiring.natCast Ring.intCast

/-- Polynomials whose monomials are packed: `add k d v p` is `k * m + p`, where the exponent of
the variable `i` in `m` is the `i`-th digit of `v` in base `B`, and `d` is the degree of `m`. -/
inductive PPoly where
  | num (k : Int)
  | add (k : Int) (d : Nat) (v : Nat) (p : PPoly)

noncomputable def PPoly.addConst_k (p : PPoly) (k : Int) : PPoly :=
  Bool.rec (PPoly.rec (fun k' => .num (Int.add_k k' k)) (fun k' d v _ ih => .add k' d v ih) p) p (Int.beqZero_k k)

/-- Terms are sorted by decreasing degree, and then by increasing packed exponents, i.e.,
in decreasing `Mon.grevlex` order. -/
noncomputable def PPoly.combine_k (p₁ : PPoly) : PPoly → PPoly :=
  PPoly.rec (motive := fun _ => PPoly → PPoly)
    (fun k₁ p₂ => addConst_k p₂ k₁)
    (fun k₁ d₁ v₁ p₁ ih₁ p₂ =>
      PPoly.rec (motive := fun _ => PPoly)
        (fun k₂ => addConst_k (.add k₁ d₁ v₁ p₁) k₂)
        (fun k₂ d₂ v₂ p₂ ih₂ =>
          Bool.rec
            (Bool.rec (.add k₁ d₁ v₁ (ih₁ (.add k₂ d₂ v₂ p₂))) (.add k₂ d₂ v₂ ih₂) (Nat.blt d₁ d₂))
            (Bool.rec
              (Bool.rec (.add k₂ d₂ v₂ ih₂) (.add k₁ d₁ v₁ (ih₁ (.add k₂ d₂ v₂ p₂))) (Nat.blt v₁ v₂))
              (Bool.rec (.add (Int.add_k k₁ k₂) d₁ v₁ (ih₁ p₂)) (ih₁ p₂) (Int.beqZero_k (Int.add_k k₁ k₂)))
              (Nat.beq v₁ v₂))
            (Nat.beq d₁ d₂))
        p₂)
    p₁

noncomputable def PPoly.mulConst_k (k : Int) (p : PPoly) : PPoly :=
  Bool.rec (PPoly.rec (fun k' => .num (Int.mul_k k k')) (fun k' d v _ ih => .add (Int.mul_k k k') d v ih) p)
    (.num (Int.ofNat 0)) (Int.beqZero_k k)

noncomputable def PPoly.mulMon_k (k : Int) (d v : Nat) (p : PPoly) : PPoly :=
  PPoly.rec
    (fun k' => Bool.rec (.add (Int.mul_k k k') d v (.num (Int.ofNat 0))) (.num (Int.ofNat 0)) (Int.beqZero_k k'))
    (fun k' d' v' _ ih => .add (Int.mul_k k k') (Nat.add d d') (Nat.add v v') ih) p

noncomputable def PPoly.pairs_k (ps : List PPoly) : Option PPoly → List PPoly :=
  List.rec (motive := fun _ => Option PPoly → List PPoly)
    (fun pend => Option.rec [] (fun p => [p]) pend)
    (fun a _ ih pend => Option.rec (ih (some a)) (fun p => combine_k p a :: ih none) pend)
    ps

noncomputable def PPoly.foldr_k (ps : List PPoly) : PPoly :=
  List.rec (.num (Int.ofNat 0)) (fun a _ ih => combine_k a ih) ps

noncomputable def PPoly.sumGo_k (fuel : List PPoly) : List PPoly → PPoly :=
  List.rec (motive := fun _ => List PPoly → PPoly)
    (fun ps => foldr_k ps)
    (fun _ _ ih ps => List.rec (.num (Int.ofNat 0)) (fun a rest _ => List.rec a (fun _ _ _ => ih (pairs_k ps none)) rest) ps)
    fuel

noncomputable def PPoly.sumB_k (ps : List PPoly) : PPoly :=
  sumGo_k ps ps

noncomputable def PPoly.mulTerms_k (p₁ p₂ : PPoly) : List PPoly :=
  PPoly.rec (fun k => [p₂.mulConst_k k]) (fun k d v _ ih => p₂.mulMon_k k d v :: ih) p₁

/-- `true` if `p` is a single term without constant. -/
noncomputable def PPoly.isMon_k (p : PPoly) : Bool :=
  PPoly.rec (fun _ => false) (fun _ _ _ q _ => PPoly.rec (fun c => Int.beqZero_k c) (fun _ _ _ _ _ => false) q) p

/-- `q` multiplied by the first term of `p`. -/
noncomputable def PPoly.mulByMon_k (p q : PPoly) : PPoly :=
  PPoly.rec (fun _ => .num (Int.ofNat 0)) (fun k d v _ _ => q.mulMon_k k d v) p

noncomputable def PPoly.mulB_k (p₁ p₂ : PPoly) : PPoly :=
  PPoly.rec (motive := fun _ => PPoly) (fun k => p₂.mulConst_k k)
    (fun _ _ _ _ _ => PPoly.rec (motive := fun _ => PPoly) (fun k => p₁.mulConst_k k)
      (fun _ _ _ _ _ =>
        Bool.rec (Bool.rec (sumB_k (mulTerms_k p₁ p₂)) (p₂.mulByMon_k p₁) p₂.isMon_k)
          (p₁.mulByMon_k p₂) p₁.isMon_k)
      p₂)
    p₁

noncomputable def PPoly.powB_k (p : PPoly) (k : Nat) : PPoly :=
  Nat.rec (.num (Int.ofNat 1)) (fun k ih => Bool.rec (p.mulB_k ih) p (Nat.beq k 0)) k

/-- The polynomial of `a ^ k`, where `p` is the polynomial of `a`. -/
noncomputable def Expr.powPP_k (B : Nat) (a : Expr) (k : Nat) (p : PPoly) : PPoly :=
  Bool.rec
    (Expr.rec (motive := fun _ => PPoly) (fun n => .num (Int.pow_k n k)) (fun n => .num (Int.ofNat (Nat.pow n k))) (fun n => .num (Int.pow_k n k))
      (fun x => .add (Int.ofNat 1) k (Nat.mul k (Nat.pow B x)) (.num (Int.ofNat 0)))
      (fun _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ => p.powB_k k)
      a)
    (.num (Int.ofNat 1))
    (Nat.beq k 0)

/-- `toPPAcc_k B e acc` is the polynomial of `e + acc`. Sums are added from the right into the
accumulator, so a sum of terms in decreasing order is normalized in linear time. -/
noncomputable def Expr.toPPAcc_k (B : Nat) (e : Expr) : PPoly → PPoly :=
  Expr.rec (motive := fun _ => PPoly → PPoly)
    (fun k acc => acc.addConst_k k)
    (fun k acc => acc.addConst_k (Int.ofNat k))
    (fun k acc => acc.addConst_k k)
    (fun x acc => PPoly.combine_k (.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))) acc)
    (fun _ ih acc => PPoly.combine_k ((ih (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc)
    (fun _ _ ih₁ ih₂ acc => ih₁ (ih₂ acc))
    (fun _ _ ih₁ ih₂ acc => ih₁ (PPoly.combine_k ((ih₂ (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc))
    (fun _ _ ih₁ ih₂ acc => PPoly.combine_k (PPoly.mulB_k (ih₁ (.num (Int.ofNat 0))) (ih₂ (.num (Int.ofNat 0)))) acc)
    (fun a k ih acc => PPoly.combine_k (a.powPP_k B k (ih (.num (Int.ofNat 0)))) acc)
    e

noncomputable def Expr.toPP_k (B : Nat) (e : Expr) : PPoly :=
  e.toPPAcc_k B (.num (Int.ofNat 0))

/-- `p`, negated if `s`. -/
noncomputable def PPoly.signB_k (p : PPoly) (s : Bool) : PPoly :=
  Bool.rec p (p.mulConst_k (Int.negSucc 0)) s

/--
`sumsPP_k B e s acc` prepends to `acc` the polynomials of the summands of `e`, negated if `s`.
-/
noncomputable def Expr.sumsPP_k (B : Nat) (e : Expr) : Bool → List PPoly → List PPoly :=
  Expr.rec (motive := fun _ => Bool → List PPoly → List PPoly)
    (fun k s acc => PPoly.signB_k (.num k) s :: acc)
    (fun k s acc => PPoly.signB_k (.num (Int.ofNat k)) s :: acc)
    (fun k s acc => PPoly.signB_k (.num k) s :: acc)
    (fun x s acc => PPoly.signB_k (.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))) s :: acc)
    (fun _ ih s acc => ih (Bool.rec true false s) acc)
    (fun _ _ ih₁ ih₂ s acc => ih₁ s (ih₂ s acc))
    (fun _ _ ih₁ ih₂ s acc => ih₁ s (ih₂ (Bool.rec true false s) acc))
    (fun _ _ ih₁ ih₂ s acc => PPoly.signB_k (PPoly.mulB_k (PPoly.sumB_k (ih₁ false [])) (PPoly.sumB_k (ih₂ false []))) s :: acc)
    (fun a k ih s acc => PPoly.signB_k (a.powPP_k B k (PPoly.sumB_k (ih false []))) s :: acc)
    e

/-- The polynomial of `e`, adding the summands pairwise. -/
noncomputable def Expr.toPPB_k (B : Nat) (e : Expr) : PPoly :=
  PPoly.sumB_k (e.sumsPP_k B false [])

noncomputable def Expr.toPPX_k (B : Nat) (bal : Bool) (e : Expr) : PPoly :=
  Bool.rec (e.toPP_k B) (e.toPPB_k B) bal

/-- An upper bound on the degree of the monomials of `e`. -/
noncomputable def Expr.degB_k (e : Expr) : Nat :=
  Expr.rec (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ ih => ih)
    (fun _ _ ih₁ ih₂ => Bool.rec ih₁ ih₂ (Nat.blt ih₁ ih₂))
    (fun _ _ ih₁ ih₂ => Bool.rec ih₁ ih₂ (Nat.blt ih₁ ih₂))
    (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂)
    (fun _ k ih => Nat.mul ih k)
    e

/-- The sum of the digits of `v` in base `B`. -/
def PPoly.dsum (B : Nat) (v : Nat) : Nat :=
  if _h : 1 < B ∧ 0 < v then v % B + dsum B (v / B) else 0
termination_by v
decreasing_by exact Nat.div_lt_self _h.2 _h.1

/-- The monomial whose exponent of the variable `i + j` is the `j`-th digit of `v` in base `B`. -/
noncomputable def PPoly.monDenote {α} [Semiring α] (ctx : Context α) (B : Nat) (i v : Nat) : α :=
  if _h : 1 < B ∧ 0 < v then (Var.denote ctx i) ^ (v % B) * monDenote ctx B (i + 1) (v / B) else 1
termination_by v
decreasing_by exact Nat.div_lt_self _h.2 _h.1

theorem PPoly.dsum_zero (B : Nat) : dsum B 0 = 0 := by
  rw [dsum]; simp

theorem PPoly.dsum_eq (hB : 1 < B) (v : Nat) : dsum B v = v % B + dsum B (v / B) := by
  rw [dsum]
  split
  · rfl
  · have : v = 0 := by omega
    subst this; simp [dsum_zero]

theorem PPoly.monDenote_zero {α} [Semiring α] (ctx : Context α) (B i : Nat) : monDenote ctx B i 0 = 1 := by
  rw [monDenote]; simp

theorem PPoly.monDenote_eq {α} [Semiring α] (ctx : Context α) (hB : 1 < B) (i v : Nat) :
    monDenote ctx B i v = (Var.denote ctx i) ^ (v % B) * monDenote ctx B (i + 1) (v / B) := by
  rw [monDenote]
  split
  · rfl
  · have : v = 0 := by omega
    subst this; simp [monDenote_zero, pow_zero, mul_one]

theorem PPoly.mod_le_dsum (hB : 1 < B) (v : Nat) : v % B ≤ dsum B v := by
  rw [dsum_eq hB]; omega

theorem PPoly.dsum_div_le (hB : 1 < B) (v : Nat) : dsum B (v / B) ≤ dsum B v := by
  rw [dsum_eq hB v]; omega

/-- Adding numbers whose digit sums add up to less than `B` adds their digits without carries. -/
theorem PPoly.add_mod_div (hB : 1 < B) (v₁ v₂ : Nat) (h : v₁ % B + v₂ % B < B) :
    (v₁ + v₂) % B = v₁ % B + v₂ % B ∧ (v₁ + v₂) / B = v₁ / B + v₂ / B := by
  have hB0 : 0 < B := by omega
  have e : v₁ + v₂ = (v₁ % B + v₂ % B) + B * (v₁ / B + v₂ / B) := by
    have h₁ := Nat.mod_add_div v₁ B
    have h₂ := Nat.mod_add_div v₂ B
    rw [Nat.mul_add]; omega
  constructor
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  · rw [e, Nat.add_mul_div_left _ _ hB0, Nat.div_eq_of_lt h, Nat.zero_add]

theorem PPoly.dsum_add (hB : 1 < B) (v₁ v₂ : Nat) (h : dsum B v₁ + dsum B v₂ < B) :
    dsum B (v₁ + v₂) = dsum B v₁ + dsum B v₂ := by
  induction v₁ using Nat.strongRecOn generalizing v₂ with
  | _ v₁ ih =>
    by_cases h₀ : v₁ = 0
    · subst h₀; simp [dsum_zero]
    have hr := add_mod_div hB v₁ v₂ (by have := mod_le_dsum hB v₁; have := mod_le_dsum hB v₂; omega)
    have hq := ih (v₁ / B) (Nat.div_lt_self (by omega) hB) (v₂ / B)
      (by have := dsum_div_le hB v₁; have := dsum_div_le hB v₂; omega)
    rw [dsum_eq hB (v₁ + v₂), hr.1, hr.2, hq, dsum_eq hB v₁, dsum_eq hB v₂]
    omega

theorem PPoly.monDenote_add {α} [CommSemiring α] (ctx : Context α) (hB : 1 < B) (i v₁ v₂ : Nat)
    (h : dsum B v₁ + dsum B v₂ < B) :
    monDenote ctx B i (v₁ + v₂) = monDenote ctx B i v₁ * monDenote ctx B i v₂ := by
  induction v₁ using Nat.strongRecOn generalizing v₂ i with
  | _ v₁ ih =>
    by_cases h₀ : v₁ = 0
    · subst h₀; simp [monDenote_zero, one_mul]
    have hr := add_mod_div hB v₁ v₂ (by have := mod_le_dsum hB v₁; have := mod_le_dsum hB v₂; omega)
    have hq := ih (v₁ / B) (Nat.div_lt_self (by omega) hB) (i + 1) (v₂ / B)
      (by have := dsum_div_le hB v₁; have := dsum_div_le hB v₂; omega)
    rw [monDenote_eq ctx hB i (v₁ + v₂), hr.1, hr.2, hq, monDenote_eq ctx hB i v₁, monDenote_eq ctx hB i v₂, pow_add]
    simp only [mul_assoc, mul_left_comm]

theorem PPoly.dsum_mul_pow (hB : 1 < B) (x k : Nat) (hk : k < B) : dsum B (k * B ^ x) = k := by
  induction x with
  | zero => rw [Nat.pow_zero, Nat.mul_one, dsum_eq hB, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk, dsum_zero]; rfl
  | succ x ih =>
    by_cases hk0 : k = 0
    · subst hk0; simp [dsum_zero]
    rw [dsum_eq hB, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left, Nat.mul_div_cancel _ (by omega), ih, Nat.zero_add]

theorem PPoly.monDenote_mul_pow {α} [Semiring α] (ctx : Context α) (hB : 1 < B) (i x k : Nat) (hk : k < B) :
    monDenote ctx B i (k * B ^ x) = Var.denote ctx (i + x) ^ k := by
  induction x generalizing i with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one, monDenote_eq ctx hB, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk, monDenote_zero, mul_one]; rfl
  | succ x ih =>
    by_cases hk0 : k = 0
    · subst hk0; simp [monDenote_zero, pow_zero]
    rw [monDenote_eq ctx hB, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left, Nat.mul_div_cancel _ (by omega), ih,
      pow_zero, one_mul, Nat.add_assoc, Nat.add_comm 1 x]

noncomputable def PPoly.denote {α} [Ring α] (ctx : Context α) (B : Nat) : PPoly → α
  | .num k => (k : α)
  | .add k _ v p => (k : α) * monDenote ctx B 0 v + denote ctx B p

/-- All the monomials of the polynomial have degree at most `D`. -/
def PPoly.Deg (B D : Nat) : PPoly → Prop
  | .num _ => True
  | .add _ _ v p => dsum B v ≤ D ∧ Deg B D p

theorem PPoly.Deg.mono {B D D' : Nat} (h : D ≤ D') : (p : PPoly) → p.Deg B D → p.Deg B D'
  | .num _, _ => trivial
  | .add _ _ _ p, ⟨h₁, h₂⟩ => ⟨by omega, Deg.mono h p h₂⟩

theorem PPoly.addConst_k_spec {α} [Ring α] (ctx : Context α) (B D : Nat) (p : PPoly) (k : Int) :
    (p.addConst_k k).denote ctx B = p.denote ctx B + k ∧ (p.Deg B D → (p.addConst_k k).Deg B D) := by
  unfold addConst_k
  cases h : Int.beqZero_k k
  · dsimp only
    induction p with
    | num k' => simp [denote, Deg, intCast_add]
    | add k' d v p ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      refine ⟨?_, fun hd => ⟨hd.1, ih₂ hd.2⟩⟩
      show (k' : α) * _ + _ = ((k' : α) * _ + denote ctx B p) + _
      rw [ih₁, add_assoc]
  · simp at h; subst h
    exact ⟨by simp [intCast_zero, add_zero], id⟩

theorem PPoly.combine_k_spec {α} [Ring α] (ctx : Context α) (B D : Nat) (p₁ p₂ : PPoly) :
    (p₁.combine_k p₂).denote ctx B = p₁.denote ctx B + p₂.denote ctx B ∧
    (p₁.Deg B D → p₂.Deg B D → (p₁.combine_k p₂).Deg B D) := by
  induction p₁ generalizing p₂ with
  | num k₁ =>
    have := addConst_k_spec ctx B D p₂ k₁
    exact ⟨by rw [add_comm]; exact this.1, fun _ h => this.2 h⟩
  | add k₁ d₁ v₁ p₁ ih₁ =>
    induction p₂ with
    | num k₂ =>
      have := addConst_k_spec ctx B D (.add k₁ d₁ v₁ p₁) k₂
      exact ⟨this.1, fun h _ => this.2 h⟩
    | add k₂ d₂ v₂ p₂ ih₂ =>
      have e : (PPoly.add k₁ d₁ v₁ p₁).combine_k (.add k₂ d₂ v₂ p₂) =
          Bool.rec (motive := fun _ => PPoly)
            (Bool.rec (.add k₁ d₁ v₁ (p₁.combine_k (.add k₂ d₂ v₂ p₂))) (.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combine_k p₂)) (Nat.blt d₁ d₂))
            (Bool.rec
              (Bool.rec (.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combine_k p₂)) (.add k₁ d₁ v₁ (p₁.combine_k (.add k₂ d₂ v₂ p₂))) (Nat.blt v₁ v₂))
              (Bool.rec (.add (Int.add_k k₁ k₂) d₁ v₁ (p₁.combine_k p₂)) (p₁.combine_k p₂) (Int.beqZero_k (Int.add_k k₁ k₂)))
              (Nat.beq v₁ v₂))
            (Nat.beq d₁ d₂) := rfl
      rw [e]
      have h₁ := ih₁ (.add k₂ d₂ v₂ p₂)
      have h₁' := ih₁ p₂
      -- the cases where the first term of the second polynomial comes first
      have hsnd : (PPoly.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combine_k p₂)).denote ctx B =
          (PPoly.add k₁ d₁ v₁ p₁).denote ctx B + (PPoly.add k₂ d₂ v₂ p₂).denote ctx B ∧
          ((PPoly.add k₁ d₁ v₁ p₁).Deg B D → (PPoly.add k₂ d₂ v₂ p₂).Deg B D →
            (PPoly.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combine_k p₂)).Deg B D) := by
        refine ⟨?_, fun ha hb => ⟨hb.1, ih₂.2 ha hb.2⟩⟩
        show (k₂ : α) * _ + _ = _ + ((k₂ : α) * _ + _)
        rw [ih₂.1, add_left_comm]
      have hfst : (PPoly.add k₁ d₁ v₁ (p₁.combine_k (.add k₂ d₂ v₂ p₂))).denote ctx B =
          (PPoly.add k₁ d₁ v₁ p₁).denote ctx B + (PPoly.add k₂ d₂ v₂ p₂).denote ctx B ∧
          ((PPoly.add k₁ d₁ v₁ p₁).Deg B D → (PPoly.add k₂ d₂ v₂ p₂).Deg B D →
            (PPoly.add k₁ d₁ v₁ (p₁.combine_k (.add k₂ d₂ v₂ p₂))).Deg B D) := by
        refine ⟨?_, fun ha hb => ⟨ha.1, h₁.2 ha.2 hb⟩⟩
        show (k₁ : α) * _ + _ = ((k₁ : α) * _ + _) + _
        rw [h₁.1, add_assoc]
      cases Nat.beq d₁ d₂
      · cases Nat.blt d₁ d₂
        · exact hfst
        · exact hsnd
      · cases hv : Nat.beq v₁ v₂
        · cases Nat.blt v₁ v₂
          · exact hsnd
          · exact hfst
        · have hv : v₁ = v₂ := Nat.eq_of_beq_eq_true hv
          subst hv
          cases hk : Int.beqZero_k (Int.add_k k₁ k₂)
          · refine ⟨?_, fun ha hb => ⟨ha.1, h₁'.2 ha.2 hb.2⟩⟩
            show ((Int.add_k k₁ k₂ : Int) : α) * _ + _ = ((k₁ : α) * _ + _) + ((k₂ : α) * _ + _)
            rw [h₁'.1, Int.add_k_eq]
            show ((k₁ + k₂ : Int) : α) * _ + _ = _
            rw [intCast_add, right_distrib]
            simp only [add_assoc, add_left_comm]
          · simp at hk
            refine ⟨?_, fun ha hb => h₁'.2 ha.2 hb.2⟩
            show _ = ((k₁ : α) * _ + _) + ((k₂ : α) * _ + _)
            rw [h₁'.1]
            have : (k₁ : α) * monDenote ctx B 0 v₁ + (k₂ : α) * monDenote ctx B 0 v₁ = 0 := by
              rw [← right_distrib, ← intCast_add, show k₁ + k₂ = 0 by omega, intCast_zero, zero_mul]
            calc p₁.denote ctx B + p₂.denote ctx B
                = ((k₁ : α) * monDenote ctx B 0 v₁ + (k₂ : α) * monDenote ctx B 0 v₁) + (p₁.denote ctx B + p₂.denote ctx B) := by
                  rw [this, zero_add]
              _ = _ := by simp only [add_assoc, add_left_comm]

theorem PPoly.mulConst_k_spec {α} [Ring α] (ctx : Context α) (B D : Nat) (k : Int) (p : PPoly) :
    (p.mulConst_k k).denote ctx B = k * p.denote ctx B ∧ (p.Deg B D → (p.mulConst_k k).Deg B D) := by
  unfold mulConst_k
  cases h : Int.beqZero_k k
  · dsimp only
    induction p with
    | num k' => simp [denote, Deg, intCast_mul]
    | add k' d v p ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      refine ⟨?_, fun hd => ⟨hd.1, ih₂ hd.2⟩⟩
      show ((Int.mul_k k k' : Int) : α) * _ + _ = (k : α) * ((k' : α) * _ + denote ctx B p)
      rw [ih₁, Int.mul_k_eq]
      show ((k * k' : Int) : α) * _ + _ = _
      rw [intCast_mul, left_distrib, mul_assoc]
  · simp at h; subst h
    exact ⟨by show ((Int.ofNat 0 : Int) : α) = _; simp [intCast_zero, zero_mul], fun _ => trivial⟩

theorem PPoly.mulMon_k_spec {α} [CommRing α] (ctx : Context α) (B D₁ D₂ : Nat) (hB : 1 < B) (k : Int) (d v : Nat)
    (hv : dsum B v ≤ D₁) (hD : D₁ + D₂ < B) (p : PPoly) (hp : p.Deg B D₂) :
    (p.mulMon_k k d v).denote ctx B = k * monDenote ctx B 0 v * p.denote ctx B ∧ (p.mulMon_k k d v).Deg B (D₁ + D₂) := by
  induction p with
  | num k' =>
    unfold mulMon_k
    dsimp only
    cases h : Int.beqZero_k k'
    · refine ⟨?_, ⟨by omega, trivial⟩⟩
      show ((Int.mul_k k k' : Int) : α) * _ + ((Int.ofNat 0 : Int) : α) = _
      rw [Int.mul_k_eq]
      show ((k * k' : Int) : α) * _ + ((0 : Int) : α) = _
      rw [intCast_zero, add_zero, intCast_mul]
      show _ = _ * ((k' : Int) : α)
      simp only [mul_assoc, mul_comm, mul_left_comm]
    · simp at h; subst h
      refine ⟨?_, trivial⟩
      show ((Int.ofNat 0 : Int) : α) = _ * ((0 : Int) : α)
      simp [intCast_zero, mul_zero]
  | add k' d' v' p ih =>
    obtain ⟨ih₁, ih₂⟩ := ih hp.2
    have hs := dsum_add hB v v' (by have := hp.1; omega)
    refine ⟨?_, ⟨by rw [Nat.add_eq, hs]; have := hp.1; omega, ih₂⟩⟩
    show ((Int.mul_k k k' : Int) : α) * monDenote ctx B 0 (Nat.add v v') + (p.mulMon_k k d v).denote ctx B = _
    rw [ih₁, Int.mul_k_eq, Nat.add_eq, monDenote_add ctx hB 0 v v' (by have := hp.1; omega)]
    show ((k * k' : Int) : α) * _ + _ = _ * ((k' : α) * _ + denote ctx B p)
    rw [intCast_mul, left_distrib]
    simp only [mul_assoc, mul_left_comm]

noncomputable def PPoly.denoteList {α} [Ring α] (ctx : Context α) (B : Nat) (ps : List PPoly) : α :=
  ps.foldr (fun p acc => p.denote ctx B + acc) 0

def PPoly.DegList (B D : Nat) (ps : List PPoly) : Prop :=
  ∀ p ∈ ps, p.Deg B D

theorem PPoly.denoteList_cons {α} [Ring α] (ctx : Context α) (B : Nat) (p : PPoly) (ps : List PPoly) :
    denoteList ctx B (p :: ps) = p.denote ctx B + denoteList ctx B ps := rfl

theorem PPoly.pairs_k_spec {α} [Ring α] (ctx : Context α) (B D : Nat) (ps : List PPoly) (pend : Option PPoly) :
    denoteList ctx B (pairs_k ps pend) = (pend.elim 0 (·.denote ctx B)) + denoteList ctx B ps ∧
    (DegList B D ps → (∀ p, pend = some p → p.Deg B D) → DegList B D (pairs_k ps pend)) := by
  induction ps generalizing pend with
  | nil =>
    cases pend with
    | none => exact ⟨by simp [pairs_k, denoteList, add_zero, Option.elim], fun _ _ => by simp [pairs_k, DegList]⟩
    | some p =>
      refine ⟨by simp [pairs_k, denoteList, add_zero, Option.elim], fun _ h => ?_⟩
      intro q hq; simp [pairs_k] at hq; subst hq; exact h q rfl
  | cons a ps ih =>
    cases pend with
    | none =>
      have := ih (some a)
      refine ⟨?_, fun h₁ _ => this.2 (fun q hq => h₁ q (List.mem_cons_of_mem _ hq)) (by intro q hq; cases hq; exact h₁ a (by simp))⟩
      show denoteList ctx B (pairs_k ps (some a)) = _
      rw [this.1]; simp [Option.elim, denoteList_cons, zero_add]
    | some p =>
      have := ih none
      have hc := combine_k_spec ctx B D p a
      refine ⟨?_, fun h₁ h₂ => ?_⟩
      · show denoteList ctx B (p.combine_k a :: pairs_k ps none) = _
        rw [denoteList_cons, this.1, hc.1]; simp [Option.elim, denoteList_cons, zero_add, add_assoc]
      · intro q hq
        simp only [pairs_k, List.mem_cons] at hq
        rcases hq with hq | hq
        · subst hq; exact hc.2 (h₂ p rfl) (h₁ a (by simp))
        · exact this.2 (fun q hq => h₁ q (List.mem_cons_of_mem _ hq)) (by simp) q hq

theorem PPoly.foldr_k_spec {α} [Ring α] (ctx : Context α) (B D : Nat) (ps : List PPoly) :
    (foldr_k ps).denote ctx B = denoteList ctx B ps ∧ (DegList B D ps → (foldr_k ps).Deg B D) := by
  induction ps with
  | nil => exact ⟨by show ((Int.ofNat 0 : Int) : α) = 0; exact intCast_zero, fun _ => trivial⟩
  | cons a ps ih =>
    have hc := combine_k_spec ctx B D a (foldr_k ps)
    refine ⟨?_, fun h => hc.2 (h a (by simp)) (ih.2 (fun q hq => h q (List.mem_cons_of_mem _ hq)))⟩
    show (a.combine_k (foldr_k ps)).denote ctx B = _
    rw [hc.1, ih.1, denoteList_cons]

theorem PPoly.sumGo_k_spec {α} [Ring α] (ctx : Context α) (B D : Nat) (fuel ps : List PPoly) :
    (sumGo_k fuel ps).denote ctx B = denoteList ctx B ps ∧ (DegList B D ps → (sumGo_k fuel ps).Deg B D) := by
  induction fuel generalizing ps with
  | nil => exact foldr_k_spec ctx B D ps
  | cons _ fuel ih =>
    cases ps with
    | nil => exact ⟨by show ((Int.ofNat 0 : Int) : α) = 0; exact intCast_zero, fun _ => trivial⟩
    | cons a rest =>
      cases rest with
      | nil =>
        refine ⟨?_, fun h => h a (by simp)⟩
        show a.denote ctx B = a.denote ctx B + 0; rw [add_zero]
      | cons b rest =>
        have hp := pairs_k_spec ctx B D (a :: b :: rest) none
        have := ih (pairs_k (a :: b :: rest) none)
        refine ⟨?_, fun h => this.2 (hp.2 h (by simp))⟩
        show (sumGo_k fuel (pairs_k (a :: b :: rest) none)).denote ctx B = _
        rw [this.1, hp.1]; simp [Option.elim, zero_add]

theorem PPoly.sumB_k_spec {α} [Ring α] (ctx : Context α) (B D : Nat) (ps : List PPoly) :
    (sumB_k ps).denote ctx B = denoteList ctx B ps ∧ (DegList B D ps → (sumB_k ps).Deg B D) :=
  sumGo_k_spec ctx B D ps ps

theorem PPoly.mulTerms_k_spec {α} [CommRing α] (ctx : Context α) (B D₁ D₂ : Nat) (hB : 1 < B) (hD : D₁ + D₂ < B)
    (p₁ p₂ : PPoly) (h₁ : p₁.Deg B D₁) (h₂ : p₂.Deg B D₂) :
    denoteList ctx B (mulTerms_k p₁ p₂) = p₁.denote ctx B * p₂.denote ctx B ∧ DegList B (D₁ + D₂) (mulTerms_k p₁ p₂) := by
  induction p₁ with
  | num k =>
    have := mulConst_k_spec ctx B D₂ k p₂
    refine ⟨?_, fun q hq => ?_⟩
    · show (p₂.mulConst_k k).denote ctx B + 0 = _
      rw [add_zero, this.1]; rfl
    · simp only [mulTerms_k, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; exact Deg.mono (by omega) _ (this.2 h₂)
  | add k d v p ih =>
    have hm := mulMon_k_spec ctx B D₁ D₂ hB k d v h₁.1 hD p₂ h₂
    have ih := ih h₁.2
    refine ⟨?_, fun q hq => ?_⟩
    · show (p₂.mulMon_k k d v).denote ctx B + denoteList ctx B (mulTerms_k p p₂) = _
      rw [hm.1, ih.1]
      show _ = ((k : α) * _ + denote ctx B p) * _
      rw [right_distrib]
    · simp only [mulTerms_k, List.mem_cons] at hq
      rcases hq with hq | hq
      · subst hq; exact hm.2
      · exact ih.2 q hq

theorem PPoly.isMon_k_eq (p : PPoly) (h : p.isMon_k = true) : ∃ k d v, p = .add k d v (.num 0) := by
  cases p with
  | num => cases h
  | add k d v q =>
    cases q with
    | num c => simp [isMon_k] at h; subst h; exact ⟨k, d, v, rfl⟩
    | add => cases h

theorem PPoly.mulB_k_spec {α} [CommRing α] (ctx : Context α) (B D₁ D₂ : Nat) (hB : 1 < B) (hD : D₁ + D₂ < B)
    (p₁ p₂ : PPoly) (h₁ : p₁.Deg B D₁) (h₂ : p₂.Deg B D₂) :
    (mulB_k p₁ p₂).denote ctx B = p₁.denote ctx B * p₂.denote ctx B ∧ (mulB_k p₁ p₂).Deg B (D₁ + D₂) := by
  cases p₁ with
  | num k =>
    have := mulConst_k_spec ctx B D₂ k p₂
    exact ⟨this.1, Deg.mono (by omega) _ (this.2 h₂)⟩
  | add k₁ d₁ v₁ q₁ =>
    cases p₂ with
    | num k =>
      have := mulConst_k_spec ctx B D₁ k (.add k₁ d₁ v₁ q₁)
      refine ⟨?_, Deg.mono (by omega) _ (this.2 h₁)⟩
      show ((PPoly.add k₁ d₁ v₁ q₁).mulConst_k k).denote ctx B = _
      rw [this.1, mul_comm]; rfl
    | add k₂ d₂ v₂ q₂ =>
      rw [show mulB_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂) = Bool.rec (Bool.rec (sumB_k (mulTerms_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂)))
        (mulByMon_k (.add k₂ d₂ v₂ q₂) (.add k₁ d₁ v₁ q₁)) (isMon_k (.add k₂ d₂ v₂ q₂)))
        (mulByMon_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂)) (isMon_k (.add k₁ d₁ v₁ q₁)) from rfl]
      cases hm₁ : isMon_k (.add k₁ d₁ v₁ q₁)
      · cases hm₂ : isMon_k (.add k₂ d₂ v₂ q₂)
        · have ht := mulTerms_k_spec ctx B D₁ D₂ hB hD _ _ h₁ h₂
          have hs := sumB_k_spec ctx B (D₁ + D₂) (mulTerms_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂))
          exact ⟨by rw [hs.1, ht.1], hs.2 ht.2⟩
        · obtain ⟨k, d, v, e⟩ := isMon_k_eq _ hm₂
          rw [e] at h₂ ⊢
          have := mulMon_k_spec ctx B D₂ D₁ hB k d v h₂.1 (by omega) _ h₁
          refine ⟨?_, by rw [Nat.add_comm]; exact this.2⟩
          show ((PPoly.add k₁ d₁ v₁ q₁).mulMon_k k d v).denote ctx B = _
          rw [this.1]
          show _ = _ * ((k : α) * _ + ((0 : Int) : α))
          rw [intCast_zero, add_zero, mul_comm]
      · obtain ⟨k, d, v, e⟩ := isMon_k_eq _ hm₁
        rw [e] at h₁ ⊢
        have := mulMon_k_spec ctx B D₁ D₂ hB k d v h₁.1 hD _ h₂
        refine ⟨?_, this.2⟩
        show ((PPoly.add k₂ d₂ v₂ q₂).mulMon_k k d v).denote ctx B = _
        rw [this.1]
        show _ = ((k : α) * _ + ((0 : Int) : α)) * _
        rw [intCast_zero, add_zero]

theorem PPoly.powB_k_spec {α} [CommRing α] (ctx : Context α) (B D : Nat) (hB : 1 < B) (p : PPoly) (k : Nat)
    (hp : p.Deg B D) (hD : D * k < B) :
    (powB_k p k).denote ctx B = p.denote ctx B ^ k ∧ (powB_k p k).Deg B (D * k) := by
  induction k with
  | zero => exact ⟨by show ((Int.ofNat 1 : Int) : α) = _; rw [pow_zero]; exact intCast_one, trivial⟩
  | succ k ih =>
    rw [show powB_k p (k + 1) = Bool.rec (p.mulB_k (powB_k p k)) p (Nat.beq k 0) from rfl]
    cases hk : Nat.beq k 0
    · have ih := ih (by rw [Nat.mul_succ] at hD; omega)
      have := mulB_k_spec ctx B D (D * k) hB (by rw [Nat.mul_succ] at hD; omega) p (powB_k p k) hp ih.2
      refine ⟨?_, by rw [Nat.mul_succ, Nat.add_comm]; exact this.2⟩
      show (p.mulB_k (powB_k p k)).denote ctx B = _
      rw [this.1, ih.1, pow_succ, mul_comm]
    · have : k = 0 := Nat.eq_of_beq_eq_true hk
      subst this
      exact ⟨by rw [pow_one], by rw [Nat.mul_one]; exact hp⟩

theorem Expr.le_max_k (a b : Nat) : a ≤ Bool.rec a b (Nat.blt a b) ∧ b ≤ Bool.rec a b (Nat.blt a b) := by
  cases h : Nat.blt a b
  · exact ⟨Nat.le_refl _, Nat.le_of_not_lt (fun hlt => by rw [Nat.blt_eq.mpr hlt] at h; cases h)⟩
  · exact ⟨Nat.le_of_lt (Nat.blt_eq.mp h), Nat.le_refl _⟩

theorem Expr.toPPAcc_k_var : (Expr.var x).toPPAcc_k B acc = PPoly.combine_k (.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))) acc := rfl
theorem Expr.toPPAcc_k_neg : (Expr.neg a).toPPAcc_k B acc = PPoly.combine_k ((a.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc := rfl
theorem Expr.toPPAcc_k_add : (Expr.add a b).toPPAcc_k B acc = a.toPPAcc_k B (b.toPPAcc_k B acc) := rfl
theorem Expr.toPPAcc_k_sub : (Expr.sub a b).toPPAcc_k B acc = a.toPPAcc_k B (PPoly.combine_k ((b.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc) := rfl
theorem Expr.toPPAcc_k_mul : (Expr.mul a b).toPPAcc_k B acc = PPoly.combine_k (PPoly.mulB_k (a.toPPAcc_k B (.num (Int.ofNat 0))) (b.toPPAcc_k B (.num (Int.ofNat 0)))) acc := rfl
theorem Expr.toPPAcc_k_pow : (Expr.pow a k).toPPAcc_k B acc = PPoly.combine_k (a.powPP_k B k (a.toPPAcc_k B (.num (Int.ofNat 0)))) acc := rfl

theorem PPoly.denote_num_zero {α} [Ring α] (ctx : Context α) (B : Nat) :
    (PPoly.num (Int.ofNat 0)).denote ctx B = 0 := intCast_zero

theorem Expr.powPP_k_spec {α} [CommRing α] (ctx : Context α) (B : Nat) (hB : 1 < B) (a : Expr) (k : Nat) (p : PPoly)
    (hp : 0 < k → p.denote ctx B = a.denote ctx ∧ p.Deg B a.degB_k) (hk : a.degB_k * k < B) :
    (a.powPP_k B k p).denote ctx B = a.denote ctx ^ k ∧ (a.powPP_k B k p).Deg B (a.degB_k * k) := by
  unfold powPP_k
  cases hk0 : Nat.beq k 0
  · have hgen : (p.powB_k k).denote ctx B = a.denote ctx ^ k ∧ (p.powB_k k).Deg B (a.degB_k * k) := by
      have hp := hp (by cases k; simp at hk0; omega)
      have := PPoly.powB_k_spec ctx B a.degB_k hB p k hp.2 hk
      rw [hp.1] at this; exact this
    dsimp only
    cases a with
    | num n =>
      refine ⟨?_, trivial⟩
      show ((Int.pow_k n k : Int) : α) = denoteInt n ^ k
      rw [Int.pow_k_eq, intCast_pow, denoteInt_eq]
    | natCast n =>
      refine ⟨?_, trivial⟩
      show (((n ^ k : Nat) : Int) : α) = (NatCast.natCast n : α) ^ k
      rw [intCast_natCast]; exact Semiring.natCast_pow (α := α) n k
    | intCast n =>
      refine ⟨?_, trivial⟩
      show ((Int.pow_k n k : Int) : α) = (IntCast.intCast n : α) ^ k
      rw [Int.pow_k_eq, intCast_pow]
    | var x =>
      have hkB : k < B := by have : Expr.degB_k (.var x) * k = 1 * k := rfl; omega
      refine ⟨?_, ⟨?_, trivial⟩⟩
      · show ((Int.ofNat 1 : Int) : α) * PPoly.monDenote ctx B 0 (Nat.mul k (Nat.pow B x)) + ((Int.ofNat 0 : Int) : α) = Var.denote ctx x ^ k
        rw [show Nat.mul k (Nat.pow B x) = k * B ^ x from rfl, PPoly.monDenote_mul_pow ctx hB 0 x k hkB, Nat.zero_add]
        show ((1 : Int) : α) * _ + ((0 : Int) : α) = _
        rw [intCast_one, one_mul, intCast_zero, add_zero]
      · rw [show Nat.mul k (Nat.pow B x) = k * B ^ x from rfl, PPoly.dsum_mul_pow hB x k hkB]
        show k ≤ 1 * k; omega
    | neg _ => exact hgen
    | add _ _ => exact hgen
    | sub _ _ => exact hgen
    | mul _ _ => exact hgen
    | pow _ _ => exact hgen
  · have : k = 0 := Nat.eq_of_beq_eq_true hk0
    subst this
    exact ⟨by show ((Int.ofNat 1 : Int) : α) = _; rw [pow_zero]; exact intCast_one, trivial⟩

theorem Expr.toPPAcc_k_spec {α} [CommRing α] (ctx : Context α) (B : Nat) (hB : 1 < B) (e : Expr) :
    ∀ (D : Nat) (acc : PPoly), e.degB_k ≤ D → D < B → acc.Deg B D →
      (e.toPPAcc_k B acc).denote ctx B = e.denote ctx + acc.denote ctx B ∧ (e.toPPAcc_k B acc).Deg B D := by
  induction e with
  | num k =>
    intro D acc _ _ hacc
    have := PPoly.addConst_k_spec ctx B D acc k
    refine ⟨?_, this.2 hacc⟩
    show (acc.addConst_k k).denote ctx B = denoteInt k + _
    rw [this.1, denoteInt_eq, add_comm]
  | natCast k =>
    intro D acc _ _ hacc
    have := PPoly.addConst_k_spec ctx B D acc (Int.ofNat k)
    refine ⟨?_, this.2 hacc⟩
    show (acc.addConst_k (Int.ofNat k)).denote ctx B = NatCast.natCast k + _
    rw [this.1, add_comm]
    exact congrArg (· + _) (intCast_natCast k)
  | intCast k =>
    intro D acc _ _ hacc
    have := PPoly.addConst_k_spec ctx B D acc k
    refine ⟨?_, this.2 hacc⟩
    show (acc.addConst_k k).denote ctx B = IntCast.intCast k + _
    rw [this.1, add_comm]
  | var x =>
    intro D acc hd _ hacc
    have hx : PPoly.dsum B (Nat.pow B x) = 1 := by
      have := PPoly.dsum_mul_pow hB x 1 hB; rwa [Nat.one_mul] at this
    have := PPoly.combine_k_spec ctx B D (.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))) acc
    refine ⟨?_, this.2 ⟨by rw [hx]; exact hd, trivial⟩ hacc⟩
    rw [toPPAcc_k_var, this.1]
    show _ = Var.denote ctx x + _
    show ((Int.ofNat 1 : Int) : α) * PPoly.monDenote ctx B 0 (Nat.pow B x) + ((Int.ofNat 0 : Int) : α) + _ = _
    have hm := PPoly.monDenote_mul_pow ctx hB 0 x 1 hB
    rw [Nat.one_mul] at hm
    rw [show Nat.pow B x = B ^ x from rfl, hm, Nat.zero_add, pow_one]
    show ((1 : Int) : α) * _ + ((0 : Int) : α) + _ = _
    rw [intCast_one, one_mul, intCast_zero, add_zero]
  | neg a ih =>
    intro D acc hd hD hacc
    have ha := ih D (.num (Int.ofNat 0)) hd hD trivial
    have hn := PPoly.mulConst_k_spec ctx B D (Int.negSucc 0) (a.toPPAcc_k B (.num (Int.ofNat 0)))
    have hc := PPoly.combine_k_spec ctx B D ((a.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc
    refine ⟨?_, by rw [toPPAcc_k_neg]; exact hc.2 (hn.2 ha.2) hacc⟩
    rw [toPPAcc_k_neg, hc.1, hn.1, ha.1, PPoly.denote_num_zero, add_zero]
    show ((-1 : Int) : α) * _ + _ = - a.denote ctx + _
    rw [intCast_neg_one, ← neg_eq_neg_one_mul]
  | add a b iha ihb =>
    intro D acc hd hD hacc
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have hb := ihb D acc (Nat.le_trans hm.2 hd) hD hacc
    have ha := iha D (b.toPPAcc_k B acc) (Nat.le_trans hm.1 hd) hD hb.2
    refine ⟨?_, by rw [toPPAcc_k_add]; exact ha.2⟩
    rw [toPPAcc_k_add, ha.1, hb.1]
    show _ = a.denote ctx + b.denote ctx + _
    rw [add_assoc]
  | sub a b iha ihb =>
    intro D acc hd hD hacc
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have hb := ihb D (.num (Int.ofNat 0)) (Nat.le_trans hm.2 hd) hD trivial
    have hn := PPoly.mulConst_k_spec ctx B D (Int.negSucc 0) (b.toPPAcc_k B (.num (Int.ofNat 0)))
    have hc := PPoly.combine_k_spec ctx B D ((b.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc
    have ha := iha D _ (Nat.le_trans hm.1 hd) hD (hc.2 (hn.2 hb.2) hacc)
    refine ⟨?_, by rw [toPPAcc_k_sub]; exact ha.2⟩
    rw [toPPAcc_k_sub, ha.1, hc.1, hn.1, hb.1, PPoly.denote_num_zero, add_zero]
    show _ + (((-1 : Int) : α) * _ + _) = a.denote ctx - b.denote ctx + _
    rw [sub_eq_add_neg, add_assoc]
    rw [intCast_neg_one, ← neg_eq_neg_one_mul]
  | mul a b iha ihb =>
    intro D acc hd hD hacc
    have ha := iha a.degB_k (.num (Int.ofNat 0)) (Nat.le_refl _) (by have : a.degB_k + b.degB_k ≤ D := hd; omega) trivial
    have hb := ihb b.degB_k (.num (Int.ofNat 0)) (Nat.le_refl _) (by have : a.degB_k + b.degB_k ≤ D := hd; omega) trivial
    have hp := PPoly.mulB_k_spec ctx B a.degB_k b.degB_k hB (by have : a.degB_k + b.degB_k ≤ D := hd; omega) _ _ ha.2 hb.2
    have hc := PPoly.combine_k_spec ctx B D (PPoly.mulB_k (a.toPPAcc_k B (.num (Int.ofNat 0))) (b.toPPAcc_k B (.num (Int.ofNat 0)))) acc
    refine ⟨?_, by rw [toPPAcc_k_mul]; exact hc.2 (PPoly.Deg.mono hd _ hp.2) hacc⟩
    rw [toPPAcc_k_mul, hc.1, hp.1, ha.1, hb.1, PPoly.denote_num_zero, add_zero, add_zero]; rfl
  | pow a k ih =>
    intro D acc hd hD hacc
    have hd' : a.degB_k * k ≤ D := hd
    have hp := powPP_k_spec ctx B hB a k (a.toPPAcc_k B (.num (Int.ofNat 0))) (fun hk => by
      have := ih a.degB_k (.num (Int.ofNat 0)) (Nat.le_refl _)
        (by have : a.degB_k ≤ a.degB_k * k := Nat.le_mul_of_pos_right _ hk; omega) trivial
      rw [PPoly.denote_num_zero, add_zero] at this; exact this) (by omega)
    have hc := PPoly.combine_k_spec ctx B D (a.powPP_k B k (a.toPPAcc_k B (.num (Int.ofNat 0)))) acc
    rw [toPPAcc_k_pow]
    exact ⟨by rw [hc.1, hp.1]; rfl, hc.2 (PPoly.Deg.mono hd' _ hp.2) hacc⟩

theorem Expr.denote_toPP_k {α} [CommRing α] (ctx : Context α) (B : Nat) (hB : 1 < B) (e : Expr) (he : e.degB_k < B) :
    (e.toPP_k B).denote ctx B = e.denote ctx := by
  have := toPPAcc_k_spec ctx B hB e e.degB_k (.num (Int.ofNat 0)) (Nat.le_refl _) he trivial
  rw [Expr.toPP_k, this.1, PPoly.denote_num_zero, add_zero]

theorem Expr.eq_of_toPP_eq {α} [CommRing α] (ctx : Context α) (B : Nat) (a b : Expr) (p : PPoly)
    (hB : (Nat.blt 1 B && (Nat.blt a.degB_k B && Nat.blt b.degB_k B)) = true)
    (h₁ : p = a.toPP_k B) (h₂ : p = b.toPP_k B) : a.denote ctx = b.denote ctx := by
  simp only [Bool.and_eq_true, Nat.blt_eq] at hB
  rw [← denote_toPP_k ctx B hB.1 a hB.2.1, ← denote_toPP_k ctx B hB.1 b hB.2.2, ← h₁, ← h₂]

theorem eq_true_of_toPP_eq {α} [CommRing α] (ctx : Context α) (B : Nat) (a b : Expr) (p : PPoly)
    (hB : (Nat.blt 1 B && (Nat.blt a.degB_k B && Nat.blt b.degB_k B)) = true)
    (h₁ : p = a.toPP_k B) (h₂ : p = b.toPP_k B) : (a.denote ctx = b.denote ctx) = True :=
  eq_true (Expr.eq_of_toPP_eq ctx B a b p hB h₁ h₂)

theorem PPoly.signB_k_spec {α} [Ring α] (ctx : Context α) (B D : Nat) (p : PPoly) (s : Bool) :
    (p.signB_k s).denote ctx B = Bool.rec (p.denote ctx B) (- p.denote ctx B) s ∧ (p.Deg B D → (p.signB_k s).Deg B D) := by
  cases s
  · exact ⟨rfl, id⟩
  · have := mulConst_k_spec ctx B D (Int.negSucc 0) p
    refine ⟨?_, this.2⟩
    show (p.mulConst_k (Int.negSucc 0)).denote ctx B = _
    rw [this.1]
    show ((-1 : Int) : α) * _ = _
    rw [intCast_neg_one, ← neg_eq_neg_one_mul]

theorem PPoly.DegList.cons {B D : Nat} {p : PPoly} {ps : List PPoly} (h₁ : p.Deg B D) (h₂ : DegList B D ps) :
    DegList B D (p :: ps) := by
  intro q hq
  simp only [List.mem_cons] at hq
  rcases hq with hq | hq
  · subst hq; exact h₁
  · exact h₂ q hq

theorem Expr.sumsPP_k_mul : (Expr.mul a b).sumsPP_k B s acc =
    PPoly.signB_k (PPoly.mulB_k (PPoly.sumB_k (a.sumsPP_k B false [])) (PPoly.sumB_k (b.sumsPP_k B false []))) s :: acc := rfl
theorem Expr.sumsPP_k_pow : (Expr.pow a k).sumsPP_k B s acc =
    PPoly.signB_k (a.powPP_k B k (PPoly.sumB_k (a.sumsPP_k B false []))) s :: acc := rfl

theorem Expr.sumsPP_k_spec {α} [CommRing α] (ctx : Context α) (B : Nat) (hB : 1 < B) (e : Expr) :
    ∀ (D : Nat) (s : Bool) (acc : List PPoly), e.degB_k ≤ D → D < B → PPoly.DegList B D acc →
      PPoly.denoteList ctx B (e.sumsPP_k B s acc) = Bool.rec (e.denote ctx) (- e.denote ctx) s + PPoly.denoteList ctx B acc ∧
      PPoly.DegList B D (e.sumsPP_k B s acc) := by
  induction e with
  | num k =>
    intro D s acc _ _ hacc
    have := PPoly.signB_k_spec ctx B D (.num k) s
    refine ⟨?_, PPoly.DegList.cons (this.2 trivial) hacc⟩
    show (PPoly.signB_k (.num k) s).denote ctx B + _ = _
    rw [this.1]
    show Bool.rec (motive := fun _ => α) (k : α) (-(k : α)) s + _ = Bool.rec (motive := fun _ => α) (denoteInt k) (-denoteInt k) s + _
    rw [denoteInt_eq]; rfl
  | natCast k =>
    intro D s acc _ _ hacc
    have := PPoly.signB_k_spec ctx B D (.num (Int.ofNat k)) s
    refine ⟨?_, PPoly.DegList.cons (this.2 trivial) hacc⟩
    show (PPoly.signB_k (.num (Int.ofNat k)) s).denote ctx B + _ = _
    rw [this.1]
    show Bool.rec (motive := fun _ => α) (((k : Int) : α)) (-((k : Int) : α)) s + _ =
      Bool.rec (motive := fun _ => α) (NatCast.natCast k) (- NatCast.natCast k) s + _
    rw [intCast_natCast]; rfl
  | intCast k =>
    intro D s acc _ _ hacc
    have := PPoly.signB_k_spec ctx B D (.num k) s
    refine ⟨?_, PPoly.DegList.cons (this.2 trivial) hacc⟩
    show (PPoly.signB_k (.num k) s).denote ctx B + _ = _
    rw [this.1]; rfl
  | var x =>
    intro D s acc hd _ hacc
    have hx : PPoly.dsum B (Nat.pow B x) = 1 := by
      have := PPoly.dsum_mul_pow hB x 1 hB; rwa [Nat.one_mul] at this
    have := PPoly.signB_k_spec ctx B D (.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))) s
    refine ⟨?_, PPoly.DegList.cons (this.2 ⟨by rw [hx]; exact hd, trivial⟩) hacc⟩
    show (PPoly.signB_k _ s).denote ctx B + _ = Bool.rec (motive := fun _ => α) (Var.denote ctx x) (- Var.denote ctx x) s + _
    rw [this.1]
    have hm := PPoly.monDenote_mul_pow ctx hB 0 x 1 hB
    rw [Nat.one_mul] at hm
    have : (PPoly.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))).denote ctx B = Var.denote ctx x := by
      show ((Int.ofNat 1 : Int) : α) * PPoly.monDenote ctx B 0 (Nat.pow B x) + ((Int.ofNat 0 : Int) : α) = _
      rw [show Nat.pow B x = B ^ x from rfl, hm, Nat.zero_add, pow_one]
      show ((1 : Int) : α) * _ + ((0 : Int) : α) = _
      rw [intCast_one, one_mul, intCast_zero, add_zero]
    rw [this]; rfl
  | neg a ih =>
    intro D s acc hd hD hacc
    have := ih D (Bool.rec true false s) acc hd hD hacc
    refine ⟨?_, this.2⟩
    show PPoly.denoteList ctx B (a.sumsPP_k B (Bool.rec true false s) acc) = Bool.rec (motive := fun _ => α) (- a.denote ctx) (- - a.denote ctx) s + _
    rw [this.1]
    cases s
    · rfl
    · show a.denote ctx + _ = - - a.denote ctx + _; rw [neg_neg]
  | add a b iha ihb =>
    intro D s acc hd hD hacc
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have hb := ihb D s acc (Nat.le_trans hm.2 hd) hD hacc
    have ha := iha D s _ (Nat.le_trans hm.1 hd) hD hb.2
    refine ⟨?_, ha.2⟩
    show PPoly.denoteList ctx B (a.sumsPP_k B s (b.sumsPP_k B s acc)) =
      Bool.rec (motive := fun _ => α) (a.denote ctx + b.denote ctx) (- (a.denote ctx + b.denote ctx)) s + _
    rw [ha.1, hb.1]
    cases s
    · show _ = _ + _ + _; rw [add_assoc]
    · show -a.denote ctx + (-b.denote ctx + _) = _; rw [neg_add, add_assoc]
  | sub a b iha ihb =>
    intro D s acc hd hD hacc
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have hb := ihb D (Bool.rec true false s) acc (Nat.le_trans hm.2 hd) hD hacc
    have ha := iha D s _ (Nat.le_trans hm.1 hd) hD hb.2
    refine ⟨?_, ha.2⟩
    show PPoly.denoteList ctx B (a.sumsPP_k B s (b.sumsPP_k B (Bool.rec true false s) acc)) =
      Bool.rec (motive := fun _ => α) (a.denote ctx - b.denote ctx) (- (a.denote ctx - b.denote ctx)) s + _
    rw [ha.1, hb.1]
    cases s
    · show a.denote ctx + (- b.denote ctx + _) = _ - _ + _; rw [sub_eq_add_neg, add_assoc]
    · show _ = -(a.denote ctx - b.denote ctx) + _
      rw [neg_sub, sub_eq_add_neg]
      show -a.denote ctx + (b.denote ctx + _) = _
      rw [add_assoc, add_left_comm]
  | mul a b iha ihb =>
    intro D s acc hd hD hacc
    have hd' : a.degB_k + b.degB_k ≤ D := hd
    have ha := iha a.degB_k false [] (Nat.le_refl _) (by omega) (fun _ h => by cases h)
    have hb := ihb b.degB_k false [] (Nat.le_refl _) (by omega) (fun _ h => by cases h)
    have hsa := PPoly.sumB_k_spec ctx B a.degB_k (a.sumsPP_k B false [])
    have hsb := PPoly.sumB_k_spec ctx B b.degB_k (b.sumsPP_k B false [])
    have hp := PPoly.mulB_k_spec ctx B a.degB_k b.degB_k hB (by omega) _ _ (hsa.2 ha.2) (hsb.2 hb.2)
    have hs := PPoly.signB_k_spec ctx B D (PPoly.mulB_k (PPoly.sumB_k (a.sumsPP_k B false [])) (PPoly.sumB_k (b.sumsPP_k B false []))) s
    rw [sumsPP_k_mul]
    refine ⟨?_, PPoly.DegList.cons (hs.2 (PPoly.Deg.mono hd' _ hp.2)) hacc⟩
    rw [PPoly.denoteList_cons, hs.1, hp.1, hsa.1, hsb.1, ha.1, hb.1]
    simp only [PPoly.denoteList, List.foldr_nil, add_zero] <;> rfl
  | pow a k ih =>
    intro D s acc hd hD hacc
    have hd' : a.degB_k * k ≤ D := hd
    have hp := Expr.powPP_k_spec ctx B hB a k (PPoly.sumB_k (a.sumsPP_k B false [])) (fun hk => by
      have ha := ih a.degB_k false [] (Nat.le_refl _)
        (by have : a.degB_k ≤ a.degB_k * k := Nat.le_mul_of_pos_right _ hk; omega) (fun _ h => by cases h)
      have hsa := PPoly.sumB_k_spec ctx B a.degB_k (a.sumsPP_k B false [])
      refine ⟨?_, hsa.2 ha.2⟩
      rw [hsa.1, ha.1]; exact add_zero _) (by omega)
    have hs := PPoly.signB_k_spec ctx B D (a.powPP_k B k (PPoly.sumB_k (a.sumsPP_k B false []))) s
    rw [sumsPP_k_pow]
    refine ⟨?_, PPoly.DegList.cons (hs.2 (PPoly.Deg.mono hd' _ hp.2)) hacc⟩
    rw [PPoly.denoteList_cons, hs.1, hp.1]; rfl

theorem Expr.denote_toPPX_k {α} [CommRing α] (ctx : Context α) (B : Nat) (hB : 1 < B) (bal : Bool) (e : Expr) (he : e.degB_k < B) :
    (e.toPPX_k B bal).denote ctx B = e.denote ctx := by
  cases bal
  · exact denote_toPP_k ctx B hB e he
  · have h := sumsPP_k_spec ctx B hB e e.degB_k false [] (Nat.le_refl _) he (fun _ h => by cases h)
    have hs := PPoly.sumB_k_spec ctx B e.degB_k (e.sumsPP_k B false [])
    show (PPoly.sumB_k (e.sumsPP_k B false [])).denote ctx B = _
    rw [hs.1, h.1]; exact add_zero _

/-- Checks the degree bound of `a` and `b` for the base `B`. -/
noncomputable def Expr.degOk_k (B : Nat) (a b : Expr) : Bool :=
  Bool.rec false (Bool.rec false (Nat.blt b.degB_k B) (Nat.blt a.degB_k B)) (Nat.blt 1 B)

theorem Expr.of_degOk_k {B : Nat} {a b : Expr} (h : degOk_k B a b = true) : 1 < B ∧ a.degB_k < B ∧ b.degB_k < B := by
  unfold degOk_k at h
  cases h₁ : Nat.blt 1 B <;> rw [h₁] at h
  · cases h
  · cases h₂ : Nat.blt a.degB_k B <;> rw [h₂] at h
    · cases h
    · exact ⟨Nat.blt_eq.mp h₁, Nat.blt_eq.mp h₂, Nat.blt_eq.mp h⟩

theorem Expr.eq_of_toPPX_eq {α} [CommRing α] (ctx : Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Expr) (p : PPoly)
    (hB : degOk_k B a b = true) (h₁ : p = a.toPPX_k B bal₁) (h₂ : p = b.toPPX_k B bal₂) : a.denote ctx = b.denote ctx := by
  have hB := of_degOk_k hB
  rw [← denote_toPPX_k ctx B hB.1 bal₁ a hB.2.1, ← denote_toPPX_k ctx B hB.1 bal₂ b hB.2.2, ← h₁, ← h₂]

theorem eq_true_of_toPPX_eq {α} [CommRing α] (ctx : Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Expr) (p : PPoly)
    (hB : Expr.degOk_k B a b = true) (h₁ : p = a.toPPX_k B bal₁) (h₂ : p = b.toPPX_k B bal₂) : (a.denote ctx = b.denote ctx) = True :=
  eq_true (Expr.eq_of_toPPX_eq ctx B bal₁ bal₂ a b p hB h₁ h₂)

theorem le_true_of_toPPX_eq {α} [CommRing α] [LE α] [IsPreorder α] (ctx : Context α) (B : Nat) (bal₁ bal₂ : Bool)
    (a b : Expr) (p : PPoly) (hB : Expr.degOk_k B a b = true) (h₁ : p = a.toPPX_k B bal₁) (h₂ : p = b.toPPX_k B bal₂) :
    (a.denote ctx ≤ b.denote ctx) = True := by
  rw [Expr.eq_of_toPPX_eq ctx B bal₁ bal₂ a b p hB h₁ h₂]; exact eq_true (Std.le_refl _)

theorem lt_false_of_toPPX_eq {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] (ctx : Context α) (B : Nat)
    (bal₁ bal₂ : Bool) (a b : Expr) (p : PPoly) (hB : Expr.degOk_k B a b = true) (h₁ : p = a.toPPX_k B bal₁)
    (h₂ : p = b.toPPX_k B bal₂) : (a.denote ctx < b.denote ctx) = False := by
  rw [Expr.eq_of_toPPX_eq ctx B bal₁ bal₂ a b p hB h₁ h₂]; exact eq_false Std.lt_irrefl

/-- The difference of `a` and `b` is the constant `k`, for the theorems `eq_false_of_sub`, `le_true_of_sub`, .... -/
theorem Expr.sub_eq_of_toPPX {α} [CommRing α] (ctx : Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Expr) (q : PPoly) (k : Int)
    (hB : degOk_k B a b = true) (h₁ : q.addConst_k k = a.toPPX_k B bal₁) (h₂ : q = b.toPPX_k B bal₂) :
    a.denote ctx - b.denote ctx = (k : α) := by
  have hB := of_degOk_k hB
  rw [← denote_toPPX_k ctx B hB.1 bal₁ a hB.2.1, ← denote_toPPX_k ctx B hB.1 bal₂ b hB.2.2, ← h₁, ← h₂,
    (PPoly.addConst_k_spec ctx B 0 q k).1, sub_eq_add_neg, add_comm, ← add_assoc, AddCommGroup.neg_add_cancel, zero_add]

/-!
Packed sums of multiples for `grind`'s Gröbner certificates (`Stepwise.simpsP`, `Stepwise.d_stepsP`).
The polynomials of the steps stay `Poly` literals and are packed by the kernel (`Poly.toPP_k`).
The operations take the normalization `nrm` of the coefficients: the identity in characteristic
zero, and the remainder modulo `c` in characteristic `c`.
-/

theorem PPoly.and_of_rec {a b : Bool} (h : Bool.rec false b a = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- The packed code of `m` in base `B`. -/
noncomputable def Mon.code_k (B : Nat) (m : Mon) : Nat :=
  Mon.rec 0 (fun pw _ ih => Nat.add (Nat.mul pw.k (Nat.pow B pw.x)) ih) m

/-- The maximum degree of the monomials of `p`. -/
noncomputable def Poly.maxDeg_k (p : Poly) : Nat :=
  Poly.rec (fun _ => 0) (fun _ m _ ih => Bool.rec ih (Mon.degree_k m) (Nat.blt ih (Mon.degree_k m))) p

/-- `p` with packed monomials, in the same order. -/
noncomputable def Poly.toPP_k (B : Nat) (p : Poly) : PPoly :=
  Poly.rec (fun k => .num k) (fun k m _ ih => .add k (Mon.degree_k m) (Mon.code_k B m) ih) p

noncomputable def PPoly.addConstN_k (nrm : Int → Int) (p : PPoly) (k : Int) : PPoly :=
  PPoly.rec (fun k' => .num (nrm (Int.add_k k' k))) (fun k' d v _ ih => .add k' d v ih) p

noncomputable def PPoly.combineN_k (nrm : Int → Int) (p₁ : PPoly) : PPoly → PPoly :=
  PPoly.rec (motive := fun _ => PPoly → PPoly)
    (fun k₁ p₂ => addConstN_k nrm p₂ k₁)
    (fun k₁ d₁ v₁ p₁ ih₁ p₂ =>
      PPoly.rec (motive := fun _ => PPoly)
        (fun k₂ => addConstN_k nrm (.add k₁ d₁ v₁ p₁) k₂)
        (fun k₂ d₂ v₂ p₂ ih₂ =>
          Bool.rec
            (Bool.rec (.add k₁ d₁ v₁ (ih₁ (.add k₂ d₂ v₂ p₂))) (.add k₂ d₂ v₂ ih₂) (Nat.blt d₁ d₂))
            (Bool.rec
              (Bool.rec (.add k₂ d₂ v₂ ih₂) (.add k₁ d₁ v₁ (ih₁ (.add k₂ d₂ v₂ p₂))) (Nat.blt v₁ v₂))
              (Bool.rec (.add (nrm (Int.add_k k₁ k₂)) d₁ v₁ (ih₁ p₂)) (ih₁ p₂) (Int.beqZero_k (nrm (Int.add_k k₁ k₂))))
              (Nat.beq v₁ v₂))
            (Nat.beq d₁ d₂))
        p₂)
    p₁

/-- `k * m * p` for the monomial `m` with degree `d` and code `v`; the constant of `p` stays a constant when `m` is `1`. -/
noncomputable def PPoly.mulMonN_k (nrm : Int → Int) (k : Int) (d v : Nat) (p : PPoly) : PPoly :=
  PPoly.rec
    (fun k' => Bool.rec (Bool.rec (.add (nrm (Int.mul_k k k')) d v (.num (Int.ofNat 0))) (.num (Int.ofNat 0)) (Int.beqZero_k (nrm (Int.mul_k k k'))))
      (.num (nrm (Int.mul_k k k'))) (Nat.beq v 0))
    (fun k' d' v' _ ih => Bool.rec (.add (nrm (Int.mul_k k k')) (Nat.add d d') (Nat.add v v') ih) ih (Int.beqZero_k (nrm (Int.mul_k k k')))) p

/--
A sum of multiples `k * m * p` of packed polynomials `p` whose monomials have degree at most `D`,
added in a balanced tree.
-/
inductive PSumTree where
  | leaf (k : Int) (m : Mon) (D : Nat) (p : PPoly)
  | node (a b : PSumTree)

noncomputable def PSumTree.eval_k (nrm : Int → Int) (B : Nat) (t : PSumTree) : PPoly :=
  PSumTree.rec (motive := fun _ => PPoly) (fun k m _ p => p.mulMonN_k nrm k (Mon.degree_k m) (Mon.code_k B m))
    (fun _ _ a b => PPoly.combineN_k nrm a b) t

/-- The degrees of the products of `t` are below `B`. -/
noncomputable def PSumTree.ok_k (B : Nat) (t : PSumTree) : Bool :=
  PSumTree.rec (motive := fun _ => Bool) (fun _ m D _ => Nat.blt (Nat.add (Mon.degree_k m) D) B)
    (fun _ _ a b => Bool.rec false b a) t

/-- Every polynomial of the leaves of `t` denotes `0`, and its monomials have degree at most `D`. -/
noncomputable def PSumTree.AllZero {α} [Ring α] (ctx : Context α) (B : Nat) (t : PSumTree) : Prop :=
  PSumTree.rec (motive := fun _ => Prop) (fun _ _ D p => p.denote ctx B = 0 ∧ p.Deg B D) (fun _ _ a b => a ∧ b) t

theorem Mon.code_k_spec {α} [CommSemiring α] (ctx : Context α) {B : Nat} (hB : 1 < B) (m : Mon) (h : m.degree < B) :
    PPoly.dsum B (m.code_k B) = m.degree ∧ PPoly.monDenote ctx B 0 (m.code_k B) = m.denote ctx := by
  induction m with
  | unit => exact ⟨PPoly.dsum_zero B, PPoly.monDenote_zero ctx B 0⟩
  | mult pw m ih =>
    have hd : pw.k + m.degree < B := h
    have ih := ih (by omega)
    have hk := PPoly.dsum_mul_pow hB pw.x pw.k (by omega)
    show PPoly.dsum B (Nat.add (Nat.mul pw.k (Nat.pow B pw.x)) (m.code_k B)) = pw.k + m.degree ∧
      PPoly.monDenote ctx B 0 (Nat.add (Nat.mul pw.k (Nat.pow B pw.x)) (m.code_k B)) = pw.denote ctx * m.denote ctx
    rw [show Nat.mul pw.k (Nat.pow B pw.x) = pw.k * B ^ pw.x from rfl, Nat.add_eq]
    refine ⟨?_, ?_⟩
    · rw [PPoly.dsum_add hB _ _ (by rw [hk, ih.1]; exact hd), hk, ih.1]
    · rw [PPoly.monDenote_add ctx hB 0 _ _ (by rw [hk, ih.1]; exact hd), PPoly.monDenote_mul_pow ctx hB 0 pw.x pw.k (by omega),
        ih.2, Nat.zero_add, Power.denote_eq]

theorem Poly.le_maxDeg_k (k : Int) (m : Mon) (p : Poly) :
    m.degree ≤ (Poly.add k m p).maxDeg_k ∧ p.maxDeg_k ≤ (Poly.add k m p).maxDeg_k := by
  show m.degree ≤ Bool.rec p.maxDeg_k (Mon.degree_k m) (Nat.blt p.maxDeg_k (Mon.degree_k m)) ∧
    p.maxDeg_k ≤ Bool.rec p.maxDeg_k (Mon.degree_k m) (Nat.blt p.maxDeg_k (Mon.degree_k m))
  rw [Mon.degree_k_eq_degree]
  have := Expr.le_max_k p.maxDeg_k m.degree
  exact ⟨this.2, this.1⟩

theorem Poly.toPP_k_spec {α} [CommRing α] (ctx : Context α) {B : Nat} (hB : 1 < B) (p : Poly) (h : p.maxDeg_k < B) :
    (p.toPP_k B).denote ctx B = p.denote ctx ∧ (p.toPP_k B).Deg B p.maxDeg_k := by
  induction p with
  | num k => exact ⟨rfl, trivial⟩
  | add k m p ih =>
    have hm := Poly.le_maxDeg_k k m p
    have ih := ih (by omega)
    have hc := Mon.code_k_spec ctx hB m (by omega)
    refine ⟨?_, ⟨by rw [hc.1]; exact hm.1, PPoly.Deg.mono hm.2 _ ih.2⟩⟩
    show (k : α) * PPoly.monDenote ctx B 0 (m.code_k B) + (p.toPP_k B).denote ctx B = k • m.denote ctx + p.denote ctx
    rw [hc.2, ih.1, zsmul_eq_intCast_mul]

section
variable {α} [Ring α] (ctx : Context α) (nrm : Int → Int) (hn : ∀ k, ((nrm k : Int) : α) = (k : α))
include hn

theorem PPoly.addConstN_k_spec (B D : Nat) (p : PPoly) (k : Int) :
    (p.addConstN_k nrm k).denote ctx B = p.denote ctx B + k ∧ (p.Deg B D → (p.addConstN_k nrm k).Deg B D) := by
  induction p with
  | num k' =>
    refine ⟨?_, fun _ => trivial⟩
    show ((nrm (Int.add_k k' k) : Int) : α) = (k' : α) + (k : α)
    rw [hn, Int.add_k_eq]; exact intCast_add k' k
  | add k' d v p ih =>
    refine ⟨?_, fun hd => ⟨hd.1, ih.2 hd.2⟩⟩
    show (k' : α) * _ + (p.addConstN_k nrm k).denote ctx B = ((k' : α) * _ + denote ctx B p) + _
    rw [ih.1, add_assoc]

theorem PPoly.combineN_k_spec (B D : Nat) (p₁ p₂ : PPoly) :
    (p₁.combineN_k nrm p₂).denote ctx B = p₁.denote ctx B + p₂.denote ctx B ∧
    (p₁.Deg B D → p₂.Deg B D → (p₁.combineN_k nrm p₂).Deg B D) := by
  induction p₁ generalizing p₂ with
  | num k₁ =>
    have := addConstN_k_spec ctx nrm hn B D p₂ k₁
    exact ⟨by rw [add_comm]; exact this.1, fun _ h => this.2 h⟩
  | add k₁ d₁ v₁ p₁ ih₁ =>
    induction p₂ with
    | num k₂ =>
      have := addConstN_k_spec ctx nrm hn B D (.add k₁ d₁ v₁ p₁) k₂
      exact ⟨this.1, fun h _ => this.2 h⟩
    | add k₂ d₂ v₂ p₂ ih₂ =>
      have e : (PPoly.add k₁ d₁ v₁ p₁).combineN_k nrm (.add k₂ d₂ v₂ p₂) =
          Bool.rec (motive := fun _ => PPoly)
            (Bool.rec (.add k₁ d₁ v₁ (p₁.combineN_k nrm (.add k₂ d₂ v₂ p₂))) (.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combineN_k nrm p₂)) (Nat.blt d₁ d₂))
            (Bool.rec
              (Bool.rec (.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combineN_k nrm p₂)) (.add k₁ d₁ v₁ (p₁.combineN_k nrm (.add k₂ d₂ v₂ p₂))) (Nat.blt v₁ v₂))
              (Bool.rec (.add (nrm (Int.add_k k₁ k₂)) d₁ v₁ (p₁.combineN_k nrm p₂)) (p₁.combineN_k nrm p₂) (Int.beqZero_k (nrm (Int.add_k k₁ k₂))))
              (Nat.beq v₁ v₂))
            (Nat.beq d₁ d₂) := rfl
      rw [e]
      have h₁ := ih₁ (.add k₂ d₂ v₂ p₂)
      have h₁' := ih₁ p₂
      have hsnd : (PPoly.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combineN_k nrm p₂)).denote ctx B =
          (PPoly.add k₁ d₁ v₁ p₁).denote ctx B + (PPoly.add k₂ d₂ v₂ p₂).denote ctx B ∧
          ((PPoly.add k₁ d₁ v₁ p₁).Deg B D → (PPoly.add k₂ d₂ v₂ p₂).Deg B D →
            (PPoly.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combineN_k nrm p₂)).Deg B D) := by
        refine ⟨?_, fun ha hb => ⟨hb.1, ih₂.2 ha hb.2⟩⟩
        show (k₂ : α) * _ + _ = _ + ((k₂ : α) * _ + _)
        rw [ih₂.1, add_left_comm]
      have hfst : (PPoly.add k₁ d₁ v₁ (p₁.combineN_k nrm (.add k₂ d₂ v₂ p₂))).denote ctx B =
          (PPoly.add k₁ d₁ v₁ p₁).denote ctx B + (PPoly.add k₂ d₂ v₂ p₂).denote ctx B ∧
          ((PPoly.add k₁ d₁ v₁ p₁).Deg B D → (PPoly.add k₂ d₂ v₂ p₂).Deg B D →
            (PPoly.add k₁ d₁ v₁ (p₁.combineN_k nrm (.add k₂ d₂ v₂ p₂))).Deg B D) := by
        refine ⟨?_, fun ha hb => ⟨ha.1, h₁.2 ha.2 hb⟩⟩
        show (k₁ : α) * _ + _ = ((k₁ : α) * _ + _) + _
        rw [h₁.1, add_assoc]
      cases Nat.beq d₁ d₂
      · cases Nat.blt d₁ d₂
        · exact hfst
        · exact hsnd
      · cases hv : Nat.beq v₁ v₂
        · cases Nat.blt v₁ v₂
          · exact hsnd
          · exact hfst
        · have hv : v₁ = v₂ := Nat.eq_of_beq_eq_true hv
          subst hv
          have hs : ((nrm (Int.add_k k₁ k₂) : Int) : α) = (k₁ : α) + (k₂ : α) := by
            rw [hn, Int.add_k_eq]; exact intCast_add k₁ k₂
          cases hk : Int.beqZero_k (nrm (Int.add_k k₁ k₂))
          · refine ⟨?_, fun ha hb => ⟨ha.1, h₁'.2 ha.2 hb.2⟩⟩
            show ((nrm (Int.add_k k₁ k₂) : Int) : α) * _ + _ = ((k₁ : α) * _ + _) + ((k₂ : α) * _ + _)
            rw [h₁'.1, hs, right_distrib]
            simp only [add_assoc, add_left_comm]
          · have hk : nrm (Int.add_k k₁ k₂) = 0 := by rw [Int.beqZero_k_eq] at hk; exact beq_iff_eq.mp hk
            refine ⟨?_, fun ha hb => h₁'.2 ha.2 hb.2⟩
            show _ = ((k₁ : α) * _ + _) + ((k₂ : α) * _ + _)
            rw [h₁'.1]
            have : (k₁ : α) * monDenote ctx B 0 v₁ + (k₂ : α) * monDenote ctx B 0 v₁ = 0 := by
              rw [← right_distrib, ← hs, hk, intCast_zero, zero_mul]
            calc p₁.denote ctx B + p₂.denote ctx B
                = ((k₁ : α) * monDenote ctx B 0 v₁ + (k₂ : α) * monDenote ctx B 0 v₁) + (p₁.denote ctx B + p₂.denote ctx B) := by
                  rw [this, zero_add]
              _ = _ := by simp only [add_assoc, add_left_comm]

end

theorem PPoly.mulMonN_k_spec {α} [CommRing α] (ctx : Context α) (nrm : Int → Int) (hn : ∀ k, ((nrm k : Int) : α) = (k : α))
    (B D₁ D₂ : Nat) (hB : 1 < B) (k : Int) (d v : Nat) (hv : dsum B v ≤ D₁) (hD : D₁ + D₂ < B) (p : PPoly) (hp : p.Deg B D₂) :
    (p.mulMonN_k nrm k d v).denote ctx B = k * monDenote ctx B 0 v * p.denote ctx B ∧ (p.mulMonN_k nrm k d v).Deg B (D₁ + D₂) := by
  induction p with
  | num k' =>
    unfold mulMonN_k
    dsimp only
    have hs : ((nrm (Int.mul_k k k') : Int) : α) = (k : α) * (k' : α) := by rw [hn, Int.mul_k_eq]; exact intCast_mul k k'
    cases hv0 : Nat.beq v 0
    case true =>
      have : v = 0 := Nat.eq_of_beq_eq_true hv0
      subst this
      refine ⟨?_, trivial⟩
      show ((nrm (Int.mul_k k k') : Int) : α) = _ * ((k' : Int) : α)
      rw [hs, monDenote_zero, mul_one]
    dsimp only
    cases h : Int.beqZero_k (nrm (Int.mul_k k k'))
    · refine ⟨?_, ⟨by omega, trivial⟩⟩
      show ((nrm (Int.mul_k k k') : Int) : α) * _ + ((Int.ofNat 0 : Int) : α) = _ * ((k' : Int) : α)
      rw [hs]
      show _ + ((0 : Int) : α) = _
      rw [intCast_zero, add_zero]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    · have h : nrm (Int.mul_k k k') = 0 := by rw [Int.beqZero_k_eq] at h; exact beq_iff_eq.mp h
      refine ⟨?_, trivial⟩
      show ((Int.ofNat 0 : Int) : α) = _ * ((k' : Int) : α)
      rw [show ((Int.ofNat 0 : Int) : α) = 0 from intCast_zero]
      have : (k : α) * (k' : α) = 0 := by rw [← hs, h, intCast_zero]
      calc (0 : α) = (k : α) * (k' : α) * monDenote ctx B 0 v := by rw [this, zero_mul]
        _ = _ := by simp only [mul_assoc, mul_comm, mul_left_comm]
  | add k' d' v' p ih =>
    obtain ⟨ih₁, ih₂⟩ := ih hp.2
    have hs : ((nrm (Int.mul_k k k') : Int) : α) = (k : α) * (k' : α) := by rw [hn, Int.mul_k_eq]; exact intCast_mul k k'
    show (Bool.rec (.add (nrm (Int.mul_k k k')) (Nat.add d d') (Nat.add v v') (p.mulMonN_k nrm k d v)) (p.mulMonN_k nrm k d v)
      (Int.beqZero_k (nrm (Int.mul_k k k'))) : PPoly).denote ctx B = _ ∧
      (Bool.rec (.add (nrm (Int.mul_k k k')) (Nat.add d d') (Nat.add v v') (p.mulMonN_k nrm k d v)) (p.mulMonN_k nrm k d v)
      (Int.beqZero_k (nrm (Int.mul_k k k'))) : PPoly).Deg B (D₁ + D₂)
    cases h : Int.beqZero_k (nrm (Int.mul_k k k'))
    · have hsum := dsum_add hB v v' (by have := hp.1; omega)
      refine ⟨?_, ⟨by rw [Nat.add_eq, hsum]; have := hp.1; omega, ih₂⟩⟩
      show ((nrm (Int.mul_k k k') : Int) : α) * monDenote ctx B 0 (Nat.add v v') + (p.mulMonN_k nrm k d v).denote ctx B =
        _ * ((k' : α) * _ + denote ctx B p)
      rw [ih₁, hs, Nat.add_eq, monDenote_add ctx hB 0 v v' (by have := hp.1; omega), left_distrib]
      simp only [mul_assoc, mul_left_comm]
    · have h : nrm (Int.mul_k k k') = 0 := by rw [Int.beqZero_k_eq] at h; exact beq_iff_eq.mp h
      refine ⟨?_, ih₂⟩
      show (p.mulMonN_k nrm k d v).denote ctx B = _ * ((k' : α) * _ + denote ctx B p)
      have : (k : α) * (k' : α) = 0 := by rw [← hs, h, intCast_zero]
      rw [ih₁, left_distrib]
      have h0 : (k : α) * monDenote ctx B 0 v * ((k' : α) * monDenote ctx B 0 v') = 0 := by
        calc (k : α) * monDenote ctx B 0 v * ((k' : α) * monDenote ctx B 0 v')
            = ((k : α) * (k' : α)) * (monDenote ctx B 0 v * monDenote ctx B 0 v') := by simp only [mul_assoc, mul_left_comm]
          _ = 0 := by rw [this, zero_mul]
      rw [h0, zero_add]

/-- The packed polynomial `P` of `p` denotes `0`, and its monomials have degree at most `p.maxDeg_k`. -/
theorem PSumTree.leaf_zero {α} [CommRing α] (ctx : Context α) (B : Nat) (p : Poly) (P : PPoly)
    (hB : Bool.rec false (Nat.blt p.maxDeg_k B) (Nat.blt 1 B) = true) (h : P = p.toPP_k B) (hp : p.denote ctx = 0) :
    P.denote ctx B = 0 ∧ P.Deg B p.maxDeg_k := by
  have hB := PPoly.and_of_rec hB
  have := Poly.toPP_k_spec ctx (Nat.blt_eq.mp hB.1) p (Nat.blt_eq.mp hB.2)
  rw [h, this.1, hp]; exact ⟨rfl, this.2⟩

theorem PSumTree.eval_k_spec {α} [CommRing α] (ctx : Context α) (nrm : Int → Int) (hn : ∀ k, ((nrm k : Int) : α) = (k : α))
    {B : Nat} (hB : 1 < B) (t : PSumTree) (hok : t.ok_k B = true) (h : t.AllZero ctx B) :
    (t.eval_k nrm B).denote ctx B = 0 ∧ (t.eval_k nrm B).Deg B (B - 1) := by
  induction t with
  | leaf k m D p =>
    have hok : Nat.blt (Nat.add (Mon.degree_k m) D) B = true := hok
    rw [Nat.blt_eq, Mon.degree_k_eq_degree, Nat.add_eq] at hok
    replace h : p.denote ctx B = 0 ∧ p.Deg B D := h
    have hc := Mon.code_k_spec ctx hB m (by omega)
    have hm := PPoly.mulMonN_k_spec ctx nrm hn B m.degree D hB k (Mon.degree_k m) (m.code_k B) (by rw [hc.1]; exact Nat.le_refl _) hok _ h.2
    refine ⟨?_, PPoly.Deg.mono (by omega) _ hm.2⟩
    show (p.mulMonN_k nrm k (Mon.degree_k m) (m.code_k B)).denote ctx B = 0
    rw [hm.1, h.1, mul_zero]
  | node a b iha ihb =>
    have hok : Bool.rec false (b.ok_k B) (a.ok_k B) = true := hok
    have hok := PPoly.and_of_rec hok
    obtain ⟨ha, hb⟩ := h
    have ha := iha hok.1 ha
    have hb := ihb hok.2 hb
    have hc := PPoly.combineN_k_spec ctx nrm hn B (B - 1) (a.eval_k nrm B) (b.eval_k nrm B)
    refine ⟨?_, hc.2 ha.2 hb.2⟩
    show (PPoly.combineN_k nrm (a.eval_k nrm B) (b.eval_k nrm B)).denote ctx B = 0
    rw [hc.1, ha.1, hb.1, add_zero]

/-- `p₁ + Σ` of the multiples `t` is `p`, checked with packed monomials. -/
theorem PSumTree.denote_eq {α} [CommRing α] (ctx : Context α) (nrm : Int → Int) (hn : ∀ k, ((nrm k : Int) : α) = (k : α))
    (B : Nat) (p₁ p : Poly) (P : PPoly) (t : PSumTree)
    (hB : Bool.rec false (Bool.rec false (Bool.rec false (t.ok_k B) (Nat.blt p₁.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt 1 B) = true)
    (h₁ : P = p.toPP_k B) (h₂ : P = (p₁.toPP_k B).combineN_k nrm (t.eval_k nrm B)) (ht : t.AllZero ctx B) :
    p.denote ctx = p₁.denote ctx := by
  have h := PPoly.and_of_rec hB
  have h' := PPoly.and_of_rec h.2
  have h'' := PPoly.and_of_rec h'.2
  have hB : 1 < B := Nat.blt_eq.mp h.1
  have he := PSumTree.eval_k_spec ctx nrm hn hB t h''.2 ht
  have hp := Poly.toPP_k_spec ctx hB p (Nat.blt_eq.mp h'.1)
  have hp₁ := Poly.toPP_k_spec ctx hB p₁ (Nat.blt_eq.mp h''.1)
  have hc := PPoly.combineN_k_spec ctx nrm hn B 0 (p₁.toPP_k B) (t.eval_k nrm B)
  rw [← hp.1, ← h₁, h₂, hc.1, he.1, hp₁.1, add_zero]

namespace Stepwise

theorem simpsP {α} [CommRing α] (ctx : Context α) (B : Nat) (p₁ p : Poly) (P : PPoly) (t : PSumTree)
    (hB : Bool.rec false (Bool.rec false (Bool.rec false (t.ok_k B) (Nat.blt p₁.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt 1 B) = true)
    (h₁ : P = p.toPP_k B) (h₂ : P = (p₁.toPP_k B).combineN_k (fun k => k) (t.eval_k (fun k => k) B)) :
    t.AllZero ctx B → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro ht h; rw [PSumTree.denote_eq ctx (fun k => k) (fun _ => rfl) B p₁ p P t hB h₁ h₂ ht, h]

theorem simpsPC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (B : Nat) (p₁ p : Poly) (P : PPoly) (t : PSumTree)
    (hB : Bool.rec false (Bool.rec false (Bool.rec false (t.ok_k B) (Nat.blt p₁.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt 1 B) = true)
    (h₁ : P = p.toPP_k B) (h₂ : P = (p₁.toPP_k B).combineN_k (fun k => Int.emod_k k (Int.ofNat c)) (t.eval_k (fun k => Int.emod_k k (Int.ofNat c)) B)) :
    t.AllZero ctx B → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro ht h
  rw [PSumTree.denote_eq ctx _ (fun k => by rw [Int.emod_k_eq, Int.ofNat_eq_natCast, IsCharP.intCast_emod]) B p₁ p P t hB h₁ h₂ ht, h]

theorem d_stepsP {α} [CommRing α] (ctx : Context α) (k : Int) (init : Poly) (B : Nat) (p₁ p : Poly) (P : PPoly) (t : PSumTree)
    (hB : Bool.rec false (Bool.rec false (Bool.rec false (t.ok_k B) (Nat.blt p₁.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt 1 B) = true)
    (h₁ : P = p.toPP_k B) (h₂ : P = (p₁.toPP_k B).combineN_k (fun k => k) (t.eval_k (fun k => k) B)) :
    t.AllZero ctx B → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro ht h; rw [PSumTree.denote_eq ctx (fun k => k) (fun _ => rfl) B p₁ p P t hB h₁ h₂ ht, h]

theorem d_stepsPC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (init : Poly) (B : Nat) (p₁ p : Poly) (P : PPoly) (t : PSumTree)
    (hB : Bool.rec false (Bool.rec false (Bool.rec false (t.ok_k B) (Nat.blt p₁.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt 1 B) = true)
    (h₁ : P = p.toPP_k B) (h₂ : P = (p₁.toPP_k B).combineN_k (fun k => Int.emod_k k (Int.ofNat c)) (t.eval_k (fun k => Int.emod_k k (Int.ofNat c)) B)) :
    t.AllZero ctx B → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro ht h
  rw [PSumTree.denote_eq ctx _ (fun k => by rw [Int.emod_k_eq, Int.ofNat_eq_natCast, IsCharP.intCast_emod]) B p₁ p P t hB h₁ h₂ ht, h]

end Stepwise

/-!
Commutative semirings with `AddRightCancel`, through the ring envelope `Ring.OfSemiring.Q`, where
`toQ` is injective.
-/

/-- `ctx` mapped by `f`. -/
noncomputable def PPoly.mapCtx {α β} (f : α → β) (ctx : Context α) : Context β :=
  RArray.rec (fun a => .leaf (f a)) (fun p _ _ l r => .branch p l r) ctx

theorem PPoly.get_mapCtx {α β} (f : α → β) (ctx : Context α) (i : Nat) : (mapCtx f ctx).get i = f (ctx.get i) := by
  induction ctx with
  | leaf a => rfl
  | branch p l r ihl ihr =>
    show Bool.rec ((mapCtx f l).get i) ((mapCtx f r).get i) (Nat.ble p i) = f (Bool.rec (l.get i) (r.get i) (Nat.ble p i))
    cases Nat.ble p i
    · exact ihl
    · exact ihr

/--
`true` if `e` has no subtraction, negation, `Int` cast or negative numeral, so that its semiring
denotation is its ring denotation.
-/
noncomputable def Expr.semi_k (e : Expr) : Bool :=
  Expr.rec (fun k => Int.rec (fun _ => true) (fun _ => false) k) (fun _ => true) (fun _ => false) (fun _ => true)
    (fun _ _ => false) (fun _ _ ih₁ ih₂ => Bool.rec false ih₂ ih₁) (fun _ _ _ _ => false)
    (fun _ _ ih₁ ih₂ => Bool.rec false ih₂ ih₁) (fun _ _ ih => ih) e

theorem Expr.semi_k_and {a b : Bool} (h : Bool.rec false b a = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem Expr.denote_mapCtx_toQ {α} [CommSemiring α] (ctx : Context α) (e : Expr) (h : e.semi_k = true) :
    e.denote (PPoly.mapCtx Ring.OfSemiring.toQ ctx) = e.denoteSAsRing ctx := by
  induction e with
  | num k =>
    cases k with
    | ofNat n => rfl
    | negSucc n => cases h
  | natCast k =>
    show NatCast.natCast k = OfNat.ofNat (α := Ring.OfSemiring.Q α) k
    exact (Semiring.ofNat_eq_natCast k).symm
  | intCast k => cases h
  | var x => exact PPoly.get_mapCtx _ ctx x
  | neg a _ => cases h
  | add a b iha ihb =>
    have h := semi_k_and h
    show a.denote _ + b.denote _ = a.denoteSAsRing ctx + b.denoteSAsRing ctx
    rw [iha h.1, ihb h.2]
  | sub a b _ _ => cases h
  | mul a b iha ihb =>
    have h := semi_k_and h
    show a.denote _ * b.denote _ = a.denoteSAsRing ctx * b.denoteSAsRing ctx
    rw [iha h.1, ihb h.2]
  | pow a k ih =>
    show a.denote _ ^ k = a.denoteSAsRing ctx ^ k
    rw [ih h]

theorem Expr.eq_of_toPPX_eqS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (B : Nat) (bal₁ bal₂ : Bool)
    (a b : Expr) (p : PPoly) (hS : Bool.rec false b.semi_k a.semi_k = true) (hB : degOk_k B a b = true)
    (h₁ : p = a.toPPX_k B bal₁) (h₂ : p = b.toPPX_k B bal₂) : a.denoteS ctx = b.denoteS ctx := by
  have hS := semi_k_and hS
  apply Ring.OfSemiring.toQ_inj
  rw [← Expr.denoteAsRing_eq, ← Expr.denoteAsRing_eq, ← denote_mapCtx_toQ ctx a hS.1, ← denote_mapCtx_toQ ctx b hS.2]
  exact Expr.eq_of_toPPX_eq _ B bal₁ bal₂ a b p hB h₁ h₂

theorem eq_true_of_toPPX_eqS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (B : Nat) (bal₁ bal₂ : Bool)
    (a b : Expr) (p : PPoly) (hS : Bool.rec false b.semi_k a.semi_k = true) (hB : Expr.degOk_k B a b = true)
    (h₁ : p = a.toPPX_k B bal₁) (h₂ : p = b.toPPX_k B bal₂) : (a.denoteS ctx = b.denoteS ctx) = True :=
  eq_true (Expr.eq_of_toPPX_eqS ctx B bal₁ bal₂ a b p hS hB h₁ h₂)

theorem le_true_of_toPPX_eqS {α} [CommSemiring α] [AddRightCancel α] [LE α] [IsPreorder α] (ctx : Context α) (B : Nat)
    (bal₁ bal₂ : Bool) (a b : Expr) (p : PPoly) (hS : Bool.rec false b.semi_k a.semi_k = true) (hB : Expr.degOk_k B a b = true)
    (h₁ : p = a.toPPX_k B bal₁) (h₂ : p = b.toPPX_k B bal₂) : (a.denoteS ctx ≤ b.denoteS ctx) = True := by
  rw [Expr.eq_of_toPPX_eqS ctx B bal₁ bal₂ a b p hS hB h₁ h₂]; exact eq_true (Std.le_refl _)

theorem lt_false_of_toPPX_eqS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    (ctx : Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Expr) (p : PPoly) (hS : Bool.rec false b.semi_k a.semi_k = true)
    (hB : Expr.degOk_k B a b = true) (h₁ : p = a.toPPX_k B bal₁) (h₂ : p = b.toPPX_k B bal₂) :
    (a.denoteS ctx < b.denoteS ctx) = False := by
  rw [Expr.eq_of_toPPX_eqS ctx B bal₁ bal₂ a b p hS hB h₁ h₂]; exact eq_false Std.lt_irrefl

end Lean.Grind.CommRing
