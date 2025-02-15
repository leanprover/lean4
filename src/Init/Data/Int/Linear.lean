/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.ByCases
import Init.Data.Prod
import Init.Data.Int.Lemmas
import Init.Data.Int.LemmasAux
import Init.Data.Int.DivModLemmas
import Init.Data.Int.Gcd
import Init.Data.RArray

namespace Int.Linear

/-! Helper definitions and theorems for constructing linear arithmetic proofs. -/

abbrev Var := Nat
abbrev Context := Lean.RArray Int

def Var.denote (ctx : Context) (v : Var) : Int :=
  ctx.get v

inductive Expr where
  | num  (v : Int)
  | var  (i : Var)
  | add  (a b : Expr)
  | sub  (a b : Expr)
  | neg (a : Expr)
  | mulL (k : Int) (a : Expr)
  | mulR (a : Expr) (k : Int)
  deriving Inhabited, BEq

def Expr.denote (ctx : Context) : Expr → Int
  | .add a b  => Int.add (denote ctx a) (denote ctx b)
  | .sub a b  => Int.sub (denote ctx a) (denote ctx b)
  | .neg a    => Int.neg (denote ctx a)
  | .num k    => k
  | .var v    => v.denote ctx
  | .mulL k e => Int.mul k (denote ctx e)
  | .mulR e k => Int.mul (denote ctx e) k

inductive Poly where
  | num (k : Int)
  | add (k : Int) (v : Var) (p : Poly)
  deriving BEq

def Poly.denote (ctx : Context) (p : Poly) : Int :=
  match p with
  | .num k => k
  | .add k v p => Int.add (Int.mul k (v.denote ctx)) (denote ctx p)

def Poly.addConst (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k+k')
  | .add k' v' p => .add k' v' (addConst p k)

def Poly.insert (k : Int) (v : Var) (p : Poly) : Poly :=
  match p with
  | .num k' => .add k v (.num k')
  | .add k' v' p =>
    bif Nat.blt v v' then
      .add k v <| .add k' v' p
    else bif Nat.beq v v' then
      if Int.add k k' == 0 then
        p
      else
        .add (Int.add k k') v' p
    else
      .add k' v' (insert k v p)

def Poly.norm (p : Poly) : Poly :=
  match p with
  | .num k => .num k
  | .add k v p => (norm p).insert k v

def Expr.toPoly' (e : Expr) :=
  go 1 e (.num 0)
where
  go (coeff : Int) : Expr → (Poly → Poly)
    | .num k    => bif k == 0 then id else (Poly.addConst · (Int.mul coeff k))
    | .var v    => (.add coeff v ·)
    | .add a b  => go coeff a ∘ go coeff b
    | .sub a b  => go coeff a ∘ go (-coeff) b
    | .mulL k a
    | .mulR a k => bif k == 0 then id else go (Int.mul coeff k) a
    | .neg a    => go (-coeff) a

def Expr.toPoly (e : Expr) : Poly :=
  e.toPoly'.norm

inductive PolyCnstr  where
  | eq (p : Poly)
  | le (p : Poly)
  deriving BEq

def PolyCnstr.denote (ctx : Context) : PolyCnstr → Prop
  | .eq p => p.denote ctx = 0
  | .le p => p.denote ctx ≤ 0

def cdiv (a b : Int) : Int :=
  -((-a)/b)

def cmod (a b : Int) : Int :=
  -((-a)%b)

theorem cdiv_add_cmod (a b : Int) : b*(cdiv a b) + cmod a b = a := by
  unfold cdiv cmod
  have := Int.ediv_add_emod (-a) b
  have := congrArg (Neg.neg) this
  simp at this
  conv => rhs; rw[← this]
  rw [Int.neg_add, ←Int.neg_mul, Int.neg_mul_comm]

theorem cmod_gt_of_pos (a : Int) {b : Int} (h : 0 < b) : cmod a b > -b :=
  Int.neg_lt_neg (Int.emod_lt_of_pos (-a) h)

theorem cmod_nonpos (a : Int) {b : Int} (h : b ≠ 0) : cmod a b ≤ 0 := by
  have := Int.neg_le_neg (Int.emod_nonneg (-a) h)
  simp at this
  assumption

theorem cmod_eq_zero_iff_emod_eq_zero (a b : Int) : cmod a b = 0 ↔ a%b = 0 := by
  unfold cmod
  have := @Int.emod_eq_emod_iff_emod_sub_eq_zero  b b a
  simp at this
  simp [Int.neg_emod, ← this, Eq.comm]

abbrev div_mul_cancel_of_mod_zero :=
  @Int.ediv_mul_cancel_of_emod_eq_zero

theorem cdiv_eq_div_of_divides {a b : Int} (h : a % b = 0) : a/b = cdiv a b := by
  replace h := div_mul_cancel_of_mod_zero h
  have hz : a % b = 0 := by
    have := Int.ediv_add_emod a b
    conv at this => rhs; rw [← Int.add_zero a]
    rw [Int.mul_comm, h] at this
    exact Int.add_left_cancel this
  have hcz : cmod a b = 0 := cmod_eq_zero_iff_emod_eq_zero a b |>.mpr hz
  have : (cdiv a b)*b = a := by
    have := cdiv_add_cmod a b
    simp [hcz] at this
    rw [Int.mul_comm] at this
    assumption
  have : (a/b)*b = (cdiv a b)*b := Eq.trans h this.symm
  by_cases h : b = 0
  next => simp[cdiv, h]
  next => rw [Int.mul_eq_mul_right_iff h] at this; assumption

def Poly.div (k : Int) : Poly → Poly
  | .num k' => .num (cdiv k' k)
  | .add k' x p => .add (k'/k) x (div k p)

def Poly.divAll (k : Int) : Poly → Bool
  | .num k' => k' % k == 0
  | .add k' _ p => k' % k == 0 && divAll k p

def Poly.divCoeffs (k : Int) : Poly → Bool
  | .num _ => true
  | .add k' _ p => k' % k == 0 && divCoeffs k p

def Poly.getConst : Poly → Int
  | .num k => k
  | .add _ _ p => getConst p

def PolyCnstr.norm : PolyCnstr → PolyCnstr
  | .eq p => .eq p.norm
  | .le p => .le p.norm

def PolyCnstr.divAll (k : Int) : PolyCnstr → Bool
  | .eq p | .le p => p.divAll k

def PolyCnstr.divCoeffs (k : Int) : PolyCnstr → Bool
  | .eq p | .le p => p.divCoeffs k

def PolyCnstr.isLe : PolyCnstr → Bool
  | .eq _ => false
  | .le _ => true

def PolyCnstr.div (k : Int) : PolyCnstr → PolyCnstr
  | .eq p => .eq <| p.div k
  | .le p => .le <| p.div k

inductive ExprCnstr  where
  | eq (p₁ p₂ : Expr)
  | le (p₁ p₂ : Expr)
  deriving Inhabited, BEq

def ExprCnstr.isLe : ExprCnstr → Bool
  | .eq .. => false
  | .le .. => true

def ExprCnstr.denote (ctx : Context) : ExprCnstr → Prop
  | .eq e₁ e₂ => e₁.denote ctx = e₂.denote ctx
  | .le e₁ e₂ => e₁.denote ctx ≤ e₂.denote ctx

def ExprCnstr.toPoly : ExprCnstr → PolyCnstr
  | .eq e₁ e₂ => .eq (e₁.sub e₂).toPoly.norm
  | .le e₁ e₂ => .le (e₁.sub e₂).toPoly.norm

-- Certificate for normalizing the coefficients of a constraint
def divBy (e e' : ExprCnstr) (k : Int) : Bool :=
  k > 0 && e.toPoly.divAll k && e'.toPoly == e.toPoly.div k

attribute [local simp] Int.add_comm Int.add_assoc Int.add_left_comm Int.add_mul Int.mul_add
attribute [local simp] Poly.insert Poly.denote Poly.norm Poly.addConst

theorem Poly.denote_addConst (ctx : Context) (p : Poly) (k : Int) : (p.addConst k).denote ctx = p.denote ctx + k := by
  induction p <;> simp [*]

attribute [local simp] Poly.denote_addConst

theorem Poly.denote_insert (ctx : Context) (k : Int) (v : Var) (p : Poly) :
    (p.insert k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  induction p <;> simp [*]
  next k' v' p' ih =>
    by_cases h₁ : Nat.blt v v' <;> simp [*]
    by_cases h₂ : Nat.beq v v' <;> simp [*]
    by_cases h₃ : k + k' = 0 <;> simp [*, Nat.eq_of_beq_eq_true h₂]
    rw [← Int.add_mul]
    simp [*]

attribute [local simp] Poly.denote_insert

theorem Poly.denote_norm (ctx : Context) (p : Poly) : p.norm.denote ctx = p.denote ctx := by
  induction p <;> simp [*]

attribute [local simp] Poly.denote_norm

private theorem sub_fold (a b : Int) : a.sub b = a - b := rfl
private theorem neg_fold (a : Int) : a.neg = -a := rfl

attribute [local simp] sub_fold neg_fold

attribute [local simp] Poly.div Poly.divAll PolyCnstr.denote

theorem Poly.denote_div_eq_of_divAll (ctx : Context) (p : Poly) (k : Int) : p.divAll k → (p.div k).denote ctx * k = p.denote ctx := by
  induction p with
  | num _ => simp; intro h; rw [← cdiv_eq_div_of_divides h]; exact div_mul_cancel_of_mod_zero h
  | add k' v p ih =>
    simp; intro h₁ h₂
    replace h₁ := div_mul_cancel_of_mod_zero h₁
    have ih := ih h₂
    simp [ih]
    apply congrArg (denote ctx p + ·)
    rw [Int.mul_right_comm, h₁]

attribute [local simp] Poly.divCoeffs Poly.getConst

theorem Poly.denote_div_eq_of_divCoeffs (ctx : Context) (p : Poly) (k : Int) : p.divCoeffs k → (p.div k).denote ctx * k + cmod p.getConst k = p.denote ctx := by
  induction p with
  | num k' => simp; rw [Int.mul_comm, cdiv_add_cmod]
  | add k' v p ih =>
    simp; intro h₁ h₂
    replace h₁ := div_mul_cancel_of_mod_zero h₁
    rw [← ih h₂]
    rw [Int.mul_right_comm, h₁, Int.add_assoc]

attribute [local simp] ExprCnstr.denote ExprCnstr.toPoly Expr.denote

theorem Expr.denote_toPoly'_go (ctx : Context) (e : Expr) :
  (toPoly'.go k e p).denote ctx = k * e.denote ctx + p.denote ctx := by
    induction k, e using Expr.toPoly'.go.induct generalizing p with
  | case1 k k' =>
    simp only [toPoly'.go]
    by_cases h : k' == 0
    · simp [h, eq_of_beq h]
    · simp [h, Var.denote]
  | case2 k i => simp [toPoly'.go]
  | case3 k a b iha ihb => simp [toPoly'.go, iha, ihb]
  | case4 k a b iha ihb =>
    simp [toPoly'.go, iha, ihb, Int.mul_sub]
    rw [Int.sub_eq_add_neg, ←Int.neg_mul, Int.add_assoc]
  | case5 k k' a ih
  | case6 k a k' ih =>
    simp only [toPoly'.go]
    by_cases h : k' == 0
    · simp [h, eq_of_beq h]
    · simp [h, cond_false, Int.mul_assoc]
      simp at ih
      rw [ih]
      rw [Int.mul_assoc, Int.mul_comm k']
  | case7 k a ih => simp [toPoly'.go, ih]

theorem Expr.denote_toPoly (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  simp [toPoly, toPoly', Expr.denote_toPoly'_go]

attribute [local simp] Expr.denote_toPoly PolyCnstr.denote

theorem ExprCnstr.denote_toPoly (ctx : Context) (c : ExprCnstr) : c.toPoly.denote ctx = c.denote ctx := by
  cases c <;> simp
  · rw [Int.sub_eq_zero]
  · constructor
    · exact Int.le_of_sub_nonpos
    · exact Int.sub_nonpos_of_le

instance : LawfulBEq Poly where
  eq_of_beq {a} := by
    induction a <;> intro b <;> cases b <;> simp_all! [BEq.beq]
    · rename_i k₁ v₁ p₁ k₂ v₂ p₂ ih
      intro _ _ h
      exact ih h
  rfl := by
    intro a
    induction a <;> simp! [BEq.beq]
    · rename_i k v p ih
      exact ih

instance : LawfulBEq PolyCnstr where
  eq_of_beq {a b} := by
    cases a <;> cases b <;> rename_i p₁ p₂ <;> simp_all! [BEq.beq]
    · show (p₁ == p₂) = true → _
      simp
    · show (p₁ == p₂) = true → _
      simp
  rfl {a} := by
    cases a <;> rename_i p <;> show (p == p) = true
      <;> simp

theorem Expr.eq_of_toPoly_eq (ctx : Context) (e e' : Expr) (h : e.toPoly == e'.toPoly) : e.denote ctx = e'.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [Poly.norm] at h
  assumption

theorem ExprCnstr.eq_of_toPoly_eq (ctx : Context) (c c' : ExprCnstr) (h : c.toPoly == c'.toPoly) : c.denote ctx = c'.denote ctx := by
  have h := congrArg (PolyCnstr.denote ctx) (eq_of_beq h)
  rw [denote_toPoly, denote_toPoly] at h
  assumption

theorem ExprCnstr.eq_of_toPoly_eq_var (ctx : Context) (x y : Var) (c : ExprCnstr) (h : c.toPoly == .eq (.add 1 x (.add (-1) y (.num 0))))
    : c.denote ctx = (x.denote ctx = y.denote ctx) := by
  have h := congrArg (PolyCnstr.denote ctx) (eq_of_beq h)
  rw [denote_toPoly] at h
  rw [h]; simp
  rw [← Int.sub_eq_add_neg, Int.sub_eq_zero]

theorem ExprCnstr.eq_of_toPoly_eq_const (ctx : Context) (x : Var) (k : Int) (c : ExprCnstr) (h : c.toPoly == .eq (.add 1 x (.num (-k))))
    : c.denote ctx = (x.denote ctx = k) := by
  have h := congrArg (PolyCnstr.denote ctx) (eq_of_beq h)
  rw [denote_toPoly] at h
  rw [h]; simp
  rw [Int.add_comm, ← Int.sub_eq_add_neg, Int.sub_eq_zero]

private theorem mul_eq_zero_iff_eq_zero (a b : Int) : b ≠ 0 → (a * b = 0 ↔ a = 0) := by
  intro h
  constructor
  · intro h'
    cases Int.mul_eq_zero.mp h'
    · assumption
    · contradiction
  · intro; simp [*]

private theorem eq_mul_le_zero {a b : Int} : 0 < b → (a ≤ 0 ↔ a * b ≤ 0) := by
  intro h
  have : 0 = 0 * b := by simp
  constructor
  · intro h'
    rw [this]
    apply Int.mul_le_mul h' <;> try simp
    apply Int.le_of_lt h
  · intro h'
    rw [this] at h'
    exact Int.le_of_mul_le_mul_right h' h

attribute [local simp] PolyCnstr.divAll PolyCnstr.div

theorem ExprCnstr.eq_of_toPoly_eq_of_divBy' (ctx : Context) (e e' : ExprCnstr) (p : PolyCnstr) (k : Int) : k > 0 → p.divAll k → e.toPoly = p → e'.toPoly = p.div k → e.denote ctx = e'.denote ctx := by
  intro h₀ h₁ h₂ h₃
  have hz : k ≠ 0 := Int.ne_of_gt h₀
  cases p <;> simp at h₁
  next p =>
    replace h₁ := Poly.denote_div_eq_of_divAll ctx p k h₁
    replace h₂ := congrArg (PolyCnstr.denote ctx) h₂
    simp only [PolyCnstr.denote.eq_1, ← h₁] at h₂
    replace h₃ := congrArg (PolyCnstr.denote ctx) h₃
    simp only [PolyCnstr.denote.eq_1, PolyCnstr.div] at h₃
    rw [mul_eq_zero_iff_eq_zero _ _ hz] at h₂
    have := Eq.trans h₂ h₃.symm
    rw [denote_toPoly, denote_toPoly] at this
    exact this
  next p =>
    replace h₁ := Poly.denote_div_eq_of_divAll ctx p k h₁
    replace h₂ := congrArg (PolyCnstr.denote ctx) h₂
    simp only [PolyCnstr.denote.eq_2, ← h₁] at h₂
    replace h₃ := congrArg (PolyCnstr.denote ctx) h₃
    simp only [PolyCnstr.denote.eq_2, PolyCnstr.div] at h₃
    rw [eq_mul_le_zero h₀] at h₃
    have := Eq.trans h₂ h₃.symm
    rw [denote_toPoly, denote_toPoly] at this
    exact this

theorem ExprCnstr.eq_of_divBy (ctx : Context) (e e' : ExprCnstr) (k : Int) : divBy e e' k → e.denote ctx = e'.denote ctx := by
  intro h
  simp only [divBy, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq] at h
  have ⟨⟨h₁, h₂⟩, h₃⟩ := h
  exact ExprCnstr.eq_of_toPoly_eq_of_divBy' ctx e e' e.toPoly k h₁ h₂ rfl h₃

private theorem mul_add_cmod_le_iff {a k b : Int} (h : k > 0) : a*k + cmod b k ≤ 0 ↔ a ≤ 0 := by
  constructor
  · intro h'
    have h₁ : a*k ≤ -cmod b k := by
      have := Int.le_sub_right_of_add_le h'
      simp at this
      assumption
    have h₂ : -cmod b k < k := by
      have := cmod_gt_of_pos b h
      have := Int.neg_lt_neg this
      simp at this
      assumption
    have h₃ : a*k < k := Int.lt_of_le_of_lt h₁ h₂
    have h₄ : a < 1 := by
      conv at h₃ => rhs; rw [← Int.one_mul k]
      have := Int.lt_of_mul_lt_mul_right h₃ (Int.le_of_lt h)
      assumption
    exact Int.le_of_lt_add_one (h₄ : a < 0 + 1)
  · intro h'
    have : a * k ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h' (Int.le_of_lt h)
    have := Int.add_le_add this (cmod_nonpos b (Int.ne_of_gt h))
    simp at this
    assumption

theorem ExprCnstr.eq_of_toPoly_eq_of_divCoeffs (ctx : Context) (e e' : ExprCnstr) (p : PolyCnstr) (k : Int) : k > 0 → p.divCoeffs k → p.isLe → e.toPoly = p → e'.toPoly = p.div k → e.denote ctx = e'.denote ctx := by
  intro h₀ h₁ h₂ h₃ h₄
  have hz : k ≠ 0 := Int.ne_of_gt h₀
  cases p <;> simp [PolyCnstr.isLe] at h₂
  clear h₂
  next p =>
    simp [PolyCnstr.divCoeffs] at h₁
    replace h₁ := Poly.denote_div_eq_of_divCoeffs ctx p k h₁
    replace h₃ := congrArg (PolyCnstr.denote ctx) h₃
    simp only [PolyCnstr.denote.eq_2, ← h₁] at h₃
    replace h₄ := congrArg (PolyCnstr.denote ctx) h₄
    simp only [PolyCnstr.denote.eq_2, PolyCnstr.div] at h₄
    rw [denote_toPoly] at h₃ h₄
    rw [h₃, h₄]
    apply propext
    apply mul_add_cmod_le_iff
    exact h₀

-- Certificate for normalizing the coefficients of inequality constraint with bound tightening
def divByLe (e e' : ExprCnstr) (k : Int) : Bool :=
  k > 0 && e.isLe && e.toPoly.divCoeffs k && e'.toPoly == e.toPoly.div k

theorem ExprCnstr.eq_of_divByLe (ctx : Context) (e e' : ExprCnstr) (k : Int) : divByLe e e' k → e.denote ctx = e'.denote ctx := by
  intro h
  simp only [divByLe, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq] at h
  have ⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩ := h
  have hle : e.toPoly.isLe := by
    cases e <;> simp [ExprCnstr.isLe] at h₁
    simp [PolyCnstr.isLe]
  apply ExprCnstr.eq_of_toPoly_eq_of_divCoeffs ctx e e' e.toPoly k h₀ h₂ hle rfl h₃

def PolyCnstr.isUnsat : PolyCnstr → Bool
  | .eq (.num k) => k != 0
  | .eq _ => false
  | .le (.num k) => k > 0
  | .le _ => false

theorem PolyCnstr.eq_false_of_isUnsat (ctx : Context) (p : PolyCnstr) : p.isUnsat → p.denote ctx = False := by
  unfold isUnsat <;> split <;> simp <;> try contradiction
  apply Int.not_le_of_gt

theorem ExprCnstr.eq_false_of_isUnsat (ctx : Context) (c : ExprCnstr) (h : c.toPoly.isUnsat) : c.denote ctx = False := by
  have := PolyCnstr.eq_false_of_isUnsat ctx (c.toPoly) h
  rw [ExprCnstr.denote_toPoly] at this
  assumption

def PolyCnstr.isUnsatCoeff (k : Int) : PolyCnstr → Bool
  | .eq p => p.divCoeffs k && k > 0 && cmod p.getConst k < 0
  | .le _ => false

private theorem contra_old {a b k : Int} (h₀ : 0 < k) (h₁ : 0 < b) (h₂ : b < k) (h₃ : a*k + b = 0) : False := by
  have : b = -a*k := by
    rw [← Int.neg_eq_of_add_eq_zero h₃, Int.neg_mul]
  rw [this] at h₁ h₂
  conv at h₂ => rhs; rw [← Int.one_mul k]
  have high := Int.lt_of_mul_lt_mul_right h₂ (Int.le_of_lt h₀)
  rw [← Int.zero_mul k] at h₁
  have low := Int.lt_of_mul_lt_mul_right h₁ (Int.le_of_lt h₀)
  replace low : 1 ≤ -a := low
  have : (1 : Int) < 1 := Int.lt_of_le_of_lt low high
  contradiction

private theorem contra {a b k : Int} (h₀ : 0 < k) (h₁ : -k < b) (h₂ : b < 0) (h₃ : a*k + b = 0) : False := by
  have : b = -a*k := by
    rw [← Int.neg_eq_of_add_eq_zero h₃, Int.neg_mul]
  rw [this, Int.neg_mul] at h₁ h₂
  replace h₁ := Int.lt_of_neg_lt_neg h₁
  replace h₂ : -(a*k) < -0 := h₂
  replace h₂ := Int.lt_of_neg_lt_neg h₂
  replace h₁ : a * k < 1 * k := by simp [h₁]
  replace h₁ : a < 1 := Int.lt_of_mul_lt_mul_right h₁ (Int.le_of_lt h₀)
  replace h₂ : 0 * k < a * k := by simp [h₂]
  replace h₂ : 0 < a := Int.lt_of_mul_lt_mul_right h₂ (Int.le_of_lt h₀)
  replace h₂ : 1 ≤ a := h₂
  have : (1 : Int) < 1 := Int.lt_of_le_of_lt h₂ h₁
  contradiction

private theorem PolyCnstr.eq_false (ctx : Context) (p : Poly) (k : Int) : p.divCoeffs k → k > 0 → cmod p.getConst k < 0 → (PolyCnstr.eq p).denote ctx = False := by
  simp
  intro h₁ h₂ h₃ h
  have hnz : k ≠ 0 := by intro h; rw [h] at h₂; contradiction
  have := Poly.denote_div_eq_of_divCoeffs ctx p k h₁
  rw [h] at this
  have low := cmod_gt_of_pos p.getConst h₂
  have high := h₃
  exact contra h₂ low high this

theorem ExprCnstr.eq_false_of_isUnsat_coeff (ctx : Context) (c : ExprCnstr) (k : Int) : c.toPoly.isUnsatCoeff k → c.denote ctx = False := by
  intro h
  cases c <;> simp [toPoly, PolyCnstr.isUnsatCoeff] at h
  next e₁ e₂ =>
    have ⟨⟨h₁, h₂⟩, h₃⟩ := h
    have := PolyCnstr.eq_false ctx _ _ h₁ h₂ h₃
    simp at this
    simp
    intro he
    simp [he] at this

def PolyCnstr.isValid : PolyCnstr → Bool
  | .eq (.num k) => k == 0
  | .eq _ => false
  | .le (.num k) => k ≤ 0
  | .le _ => false

theorem PolyCnstr.eq_true_of_isValid (ctx : Context) (p : PolyCnstr) : p.isValid → p.denote ctx = True := by
  unfold isValid <;> split <;> simp

theorem ExprCnstr.eq_true_of_isValid (ctx : Context) (c : ExprCnstr) (h : c.toPoly.isValid) : c.denote ctx = True := by
  have := PolyCnstr.eq_true_of_isValid ctx (c.toPoly) h
  rw [ExprCnstr.denote_toPoly] at this
  assumption

private def gcd (a b : Int) : Int :=
  Int.ofNat <| Int.gcd a b

private theorem gcd_dvd_left (a b : Int) : gcd a b ∣ a := by
  simp [gcd, Int.gcd_dvd_left]

private theorem gcd_dvd_right (a b : Int) : gcd a b ∣ b := by
  simp [gcd, Int.gcd_dvd_right]

private theorem gcd_dvd_step {k a b x : Int} (h : k ∣ a*x + b) : gcd a k ∣ b := by
  have h₁ : gcd a k ∣ a*x + b := Int.dvd_trans (gcd_dvd_right a k) h
  have h₂ : gcd a k ∣ a*x := Int.dvd_trans (gcd_dvd_left a k) (Int.dvd_mul_right a x)
  exact Int.dvd_iff_dvd_of_dvd_add h₁ |>.mp h₂

def Poly.gcdCoeffs : Poly → Int → Int
  | .num _, k => k
  | .add k' _ p, k => gcdCoeffs p (gcd k' k)

theorem Poly.gcd_dvd_const {ctx : Context} {p : Poly} {k : Int} (h : k ∣ p.denote ctx) : p.gcdCoeffs k ∣ p.getConst := by
  induction p generalizing k <;> simp_all [gcdCoeffs]
  next k' x p ih =>
    rw [Int.add_comm] at h
    exact ih (gcd_dvd_step h)

def Poly.mul (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k*k')
  | .add k' v p => .add (k*k') v (mul p k)

@[simp] theorem Poly.denote_mul (ctx : Context) (p : Poly) (k : Int) : (p.mul k).denote ctx = k * p.denote ctx := by
  induction p <;> simp [mul, *]
  rw [Int.mul_assoc]

structure DvdPolyCnstr where
  a : Int
  p : Poly

def DvdPolyCnstr.denote (ctx : Context) (c : DvdPolyCnstr) : Prop :=
  c.a ∣ c.p.denote ctx

def DvdPolyCnstr.isUnsat (c : DvdPolyCnstr) : Bool :=
  c.p.getConst % c.p.gcdCoeffs c.a != 0

def DvdPolyCnstr.isEqv (c₁ c₂ : DvdPolyCnstr) (k : Int) : Bool :=
  k != 0 && c₁.a == k*c₂.a && c₁.p == c₂.p.mul k

private theorem not_dvd_of_not_mod_zero {a b : Int} (h : ¬ b % a = 0) : ¬ a ∣ b := by
  intro h; have := Int.emod_eq_zero_of_dvd h; contradiction

def DvdPolyCnstr.eq_false_of_isUnsat (ctx : Context) (c : DvdPolyCnstr) : c.isUnsat → c.denote ctx = False := by
  rcases c with ⟨a, p⟩
  simp [isUnsat, denote]
  intro h₁ h₂
  have := Poly.gcd_dvd_const h₂
  have := not_dvd_of_not_mod_zero h₁
  contradiction

@[local simp] private theorem mul_dvd_mul_eq {a b c : Int} (hnz : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c := by
  constructor
  · intro h
    rcases h with ⟨k, h⟩
    rw [Int.mul_assoc a] at h
    replace h := Int.eq_of_mul_eq_mul_left hnz h
    exists k
  · intro h
    rcases h with ⟨k, h⟩
    exists k
    rw [h, Int.mul_assoc]

@[local simp] theorem DvdPolyCnstr.eq_of_isEqv (ctx : Context) (c₁ c₂ : DvdPolyCnstr) (k : Int) (h : isEqv c₁ c₂ k) : c₁.denote ctx = c₂.denote ctx := by
  rcases c₁ with ⟨a₁, e₁⟩
  rcases c₂ with ⟨a₂, e₂⟩
  simp [isEqv] at h
  rcases h with ⟨⟨h₁, h₂⟩, h₃⟩
  replace h₃ := congrArg (Poly.denote ctx) h₃
  simp at h₃
  simp [denote, *]

structure DvdCnstr where
  a : Int
  e : Expr

def DvdCnstr.denote (ctx : Context) (c : DvdCnstr) : Prop :=
  c.a ∣ c.e.denote ctx

def DvdCnstr.toPoly (c : DvdCnstr) : DvdPolyCnstr :=
  { a := c.a, p := c.e.toPoly }

@[simp] theorem DvdCnstr.denote_toPoly_eq (ctx : Context) (c : DvdCnstr) : c.denote ctx = c.toPoly.denote ctx := by
  simp [toPoly, denote, DvdPolyCnstr.denote]

def DvdCnstr.isEqv (c₁ c₂ : DvdCnstr) (k : Int) : Bool :=
  c₁.toPoly.isEqv c₂.toPoly k

def DvdCnstr.isUnsat (c : DvdCnstr) : Bool :=
  c.toPoly.isUnsat

theorem DvdCnstr.eq_of_isEqv (ctx : Context) (c₁ c₂ : DvdCnstr) (k : Int) (h : isEqv c₁ c₂ k) : c₁.denote ctx = c₂.denote ctx := by
  simp [DvdPolyCnstr.eq_of_isEqv ctx c₁.toPoly c₂.toPoly k h]

theorem DvdCnstr.eq_false_of_isUnsat (ctx : Context) (c : DvdCnstr) (h : c.isUnsat) : c.denote ctx = False := by
  simp [DvdPolyCnstr.eq_false_of_isUnsat ctx c.toPoly h]

end Int.Linear

theorem Int.not_le_eq (a b : Int) : (¬a ≤ b) = (b + 1 ≤ a) := by
  apply propext; constructor
  · intro h; have h := Int.add_one_le_of_lt (Int.lt_of_not_ge h); assumption
  · intro h; apply Int.not_le_of_gt; exact h

theorem Int.not_ge_eq (a b : Int) : (¬a ≥ b) = (a + 1 ≤ b) := by
  apply Int.not_le_eq

theorem Int.not_lt_eq (a b : Int) : (¬a < b) = (b ≤ a) := by
  apply propext; constructor
  · intro h; simp [Int.not_lt] at h; assumption
  · intro h; apply Int.not_le_of_gt; simp [Int.lt_add_one_iff, *]

theorem Int.not_gt_eq (a b : Int) : (¬a > b) = (a ≤ b) := by
  apply Int.not_lt_eq
