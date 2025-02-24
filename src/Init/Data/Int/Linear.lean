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
import Init.Data.Int.DivMod.Bootstrap
import Init.Data.Int.Gcd
import Init.Data.RArray
import Init.Data.AC

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

/--
Similar to `Poly.denote`, but produces a denotation better for `simp +arith`.
Remark: we used to convert `Poly` back into `Expr` to achieve that.
-/
def Poly.denote' (ctx : Context) (p : Poly) : Int :=
  match p with
  | .num k => k
  | .add 1 v p => go (v.denote ctx) p
  | .add k v p => go (Int.mul k (v.denote ctx)) p
where
  go (r : Int)  (p : Poly) : Int :=
    match p with
    | .num 0 => r
    | .num k => Int.add r k
    | .add 1 v p => go (Int.add r (v.denote ctx)) p
    | .add k v p => go (Int.add r (Int.mul k (v.denote ctx))) p

theorem Poly.denote'_go_eq_denote (ctx : Context) (p : Poly) (r : Int) : denote'.go ctx r p = p.denote ctx + r := by
  induction r, p using denote'.go.induct ctx <;> simp [denote'.go, denote]
  next => rw [Int.add_comm]
  next ih => simp [denote'.go] at ih; rw [ih]; ac_rfl
  next ih => simp [denote'.go] at ih; rw [ih]; ac_rfl

theorem Poly.denote'_eq_denote (ctx : Context) (p : Poly) : p.denote' ctx = p.denote ctx := by
  unfold denote' <;> split <;> simp [denote, denote'_go_eq_denote] <;> ac_rfl

theorem Poly.denote'_add (ctx : Context) (a : Int) (x : Var) (p : Poly) : (Poly.add a x p).denote' ctx = a * x.denote ctx + p.denote ctx := by
  simp [Poly.denote'_eq_denote, denote]

def Poly.addConst (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k+k')
  | .add k' v' p => .add k' v' (addConst p k)

def Poly.insert (k : Int) (v : Var) (p : Poly) : Poly :=
  match p with
  | .num k' => .add k v (.num k')
  | .add k' v' p =>
    bif Nat.blt v' v then
      .add k v <| .add k' v' p
    else bif Nat.beq v v' then
      if Int.add k k' == 0 then
        p
      else
        .add (Int.add k k') v' p
    else
      .add k' v' (insert k v p)

/-- Normalizes the given polynomial by fusing monomial and constants. -/
def Poly.norm (p : Poly) : Poly :=
  match p with
  | .num k => .num k
  | .add k v p => (norm p).insert k v

def Poly.append (p₁ p₂ : Poly) : Poly :=
  match p₁ with
  | .num k₁ => p₂.addConst k₁
  | .add k x p₁ => .add k x (append p₁ p₂)

def Poly.combine' (fuel : Nat) (p₁ p₂ : Poly) : Poly :=
  match fuel with
  | 0 => p₁.append p₂
  | fuel + 1 => match p₁, p₂ with
    | .num k₁, .num k₂ => .num (k₁+k₂)
    | .num k₁, .add a x p => .add a x (combine' fuel (.num k₁) p)
    | .add a x p, .num k₂ => .add a x (combine' fuel p (.num k₂))
    | .add a₁ x₁ p₁, .add a₂ x₂ p₂ =>
      bif Nat.beq x₁ x₂ then
        let a := a₁ + a₂
        bif a == 0 then
          combine' fuel p₁ p₂
        else
          .add a x₁ (combine' fuel p₁ p₂)
    else bif Nat.blt x₂ x₁ then
      .add a₁ x₁ (combine' fuel p₁ (.add a₂ x₂ p₂))
    else
      .add a₂ x₂ (combine' fuel (.add a₁ x₁ p₁) p₂)

def Poly.combine (p₁ p₂ : Poly) : Poly :=
  combine' 100000000 p₁ p₂

/-- Converts the given expression into a polynomial. -/
def Expr.toPoly' (e : Expr) : Poly :=
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

/-- Converts the given expression into a polynomial, and then normalizes it. -/
def Expr.norm (e : Expr) : Poly :=
  e.toPoly'.norm

/--
Returns the ceiling of the division `a / b`. That is, the result is equivalent to `⌈a / b⌉`.
Examples:
- `cdiv 7 3` returns `3`
- `cdiv (-7) 3` returns `-2`.
-/
def cdiv (a b : Int) : Int :=
  -((-a)/b)

/--
Returns the ceiling-compatible remainder of the division `a / b`.
This function ensures that the remainder is consistent with `cdiv`, meaning:
```
a = b * cdiv a b + cmod a b
```
See theorem `cdiv_add_cmod`. We also have
```
-b < cmod a b ≤ 0
```
-/
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

private abbrev div_mul_cancel_of_mod_zero :=
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

/-- Returns the constant of the given linear polynomial. -/
def Poly.getConst : Poly → Int
  | .num k => k
  | .add _ _ p => getConst p

/--
`p.div k` divides all coefficients of the polynomial `p` by `k`, but
rounds up the constant using `cdiv`.
Notes:
- We only use this function with `k`s that divides all coefficients.
- We use `cdiv` for the constant to implement the inequality tightening rule.
-/
def Poly.div (k : Int) : Poly → Poly
  | .num k' => .num (cdiv k' k)
  | .add k' x p => .add (k'/k) x (div k p)

/--
Returns `true` if `k` divides all coefficients and the constant of the given
linear polynomial.
-/
def Poly.divAll (k : Int) : Poly → Bool
  | .num k' => k' % k == 0
  | .add k' _ p => k' % k == 0 && divAll k p

/--
Returns `true` if `k` divides all coefficients of the given linear polynomial.
-/
def Poly.divCoeffs (k : Int) : Poly → Bool
  | .num _ => true
  | .add k' _ p => k' % k == 0 && divCoeffs k p

/--
`p.mul k` multiplies all coefficients and constant of the polynomial `p` by `k`.
-/
def Poly.mul (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k*k')
  | .add k' v p => .add (k*k') v (mul p k)

@[simp] theorem Poly.denote_mul (ctx : Context) (p : Poly) (k : Int) : (p.mul k).denote ctx = k * p.denote ctx := by
  induction p <;> simp [mul, denote, *]
  rw [Int.mul_assoc, Int.mul_add]

attribute [local simp] Int.add_comm Int.add_assoc Int.add_left_comm Int.add_mul Int.mul_add
attribute [local simp] Poly.insert Poly.denote Poly.norm Poly.addConst

theorem Poly.denote_addConst (ctx : Context) (p : Poly) (k : Int) : (p.addConst k).denote ctx = p.denote ctx + k := by
  induction p <;> simp [*]

attribute [local simp] Poly.denote_addConst

theorem Poly.denote_insert (ctx : Context) (k : Int) (v : Var) (p : Poly) :
    (p.insert k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  fun_induction p.insert k v <;>
    simp only [insert, cond_true, cond_false, ↓reduceIte, *] <;>
    simp_all [← Int.add_mul]

attribute [local simp] Poly.denote_insert

theorem Poly.denote_norm (ctx : Context) (p : Poly) : p.norm.denote ctx = p.denote ctx := by
  induction p <;> simp [*]

attribute [local simp] Poly.denote_norm

theorem Poly.denote_append (ctx : Context) (p₁ p₂ : Poly) : (p₁.append p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  induction p₁ <;> simp [append, *]

attribute [local simp] Poly.denote_append

theorem Poly.denote_combine' (ctx : Context) (fuel : Nat) (p₁ p₂ : Poly) : (p₁.combine' fuel p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  fun_induction p₁.combine' fuel p₂ <;>
    simp +zetaDelta only [combine', cond_true, cond_false, *] <;>
    simp_all +zetaDelta [denote, ← Int.add_mul]

theorem Poly.denote_combine (ctx : Context) (p₁ p₂ : Poly) : (p₁.combine p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  simp [combine, denote_combine']

attribute [local simp] Poly.denote_combine

theorem sub_fold (a b : Int) : a.sub b = a - b := rfl
theorem neg_fold (a : Int) : a.neg = -a := rfl

attribute [local simp] sub_fold neg_fold

attribute [local simp] Poly.div Poly.divAll

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

attribute [local simp] Expr.denote

theorem Expr.denote_toPoly'_go (ctx : Context) (e : Expr) :
  (toPoly'.go k e p).denote ctx = k * e.denote ctx + p.denote ctx := by
    induction k, e using Expr.toPoly'.go.induct generalizing p with
  | case1 k k' h =>
    simp only [toPoly'.go, h, cond_true]
    simp [eq_of_beq h]
  | case2 k k' h =>
    simp only [toPoly'.go, h, cond_false]
    simp [Var.denote]
  | case3 k i => simp [toPoly'.go]
  | case4 k a b iha ihb => simp [toPoly'.go, iha, ihb]
  | case5 k a b iha ihb =>
    simp [toPoly'.go, iha, ihb, Int.mul_sub]
    rw [Int.sub_eq_add_neg, ←Int.neg_mul, Int.add_assoc]
  | case6 k k' a h
  | case8 k a k' h =>
    simp only [toPoly'.go, h, cond_false]
    simp [eq_of_beq h]
  | case7 k a k' h ih =>
    simp only [toPoly'.go, h, cond_false]
    simpa [denote, ← Int.mul_assoc] using ih
  | case9 k a h h ih =>
    simp only [toPoly'.go, h, cond_false]
    simp only [mul_def, denote]
    rw [Int.mul_comm (denote _ _) _]
    simpa [Int.mul_assoc] using ih
  | case10 k a ih => simp [toPoly'.go, ih]

theorem Expr.denote_norm (ctx : Context) (e : Expr) : e.norm.denote ctx = e.denote ctx := by
  simp [norm, toPoly', Expr.denote_toPoly'_go]

attribute [local simp] Expr.denote_norm

instance : LawfulBEq Poly where
  eq_of_beq {a} := by
    induction a <;> intro b <;> cases b <;> simp_all! [BEq.beq]
    next ih =>
      intro _ _ h
      exact ih h
  rfl := by
    intro a
    induction a <;> simp! [BEq.beq]
    assumption

attribute [local simp] Poly.denote'_eq_denote

theorem Expr.eq_of_norm_eq (ctx : Context) (e : Expr) (p : Poly) (h : e.norm == p) : e.denote ctx = p.denote' ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [Poly.norm] at h
  simp [*]

def norm_eq_cert (lhs rhs : Expr) (p : Poly) : Bool :=
  p == (lhs.sub rhs).norm

theorem norm_eq (ctx : Context) (lhs rhs : Expr) (p : Poly) (h : norm_eq_cert lhs rhs p) : (lhs.denote ctx = rhs.denote ctx) = (p.denote' ctx = 0) := by
  simp [norm_eq_cert] at h; subst p
  simp
  rw [Int.sub_eq_zero]

theorem norm_le (ctx : Context) (lhs rhs : Expr) (p : Poly) (h : norm_eq_cert lhs rhs p) : (lhs.denote ctx ≤ rhs.denote ctx) = (p.denote' ctx ≤ 0) := by
  simp [norm_eq_cert] at h; subst p
  simp
  constructor
  · exact Int.sub_nonpos_of_le
  · exact Int.le_of_sub_nonpos

def norm_eq_var_cert (lhs rhs : Expr) (x y : Var) : Bool :=
  (lhs.sub rhs).norm == .add 1 x (.add (-1) y (.num 0))

theorem norm_eq_var (ctx : Context) (lhs rhs : Expr) (x y : Var) (h : norm_eq_var_cert lhs rhs x y)
    : (lhs.denote ctx = rhs.denote ctx) = (x.denote ctx = y.denote ctx) := by
  simp [norm_eq_var_cert] at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  rw [←Int.sub_eq_zero, h, ← @Int.sub_eq_zero (Var.denote ctx x), Int.sub_eq_add_neg]

def norm_eq_var_const_cert (lhs rhs : Expr) (x : Var) (k : Int) : Bool :=
  (lhs.sub rhs).norm == .add 1 x (.num (-k))

theorem norm_eq_var_const (ctx : Context) (lhs rhs : Expr) (x : Var) (k : Int) (h : norm_eq_var_const_cert lhs rhs x k)
    : (lhs.denote ctx = rhs.denote ctx) = (x.denote ctx = k) := by
  simp [norm_eq_var_const_cert] at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  rw [←Int.sub_eq_zero, h, Int.add_comm, ← Int.sub_eq_add_neg, Int.sub_eq_zero]

private theorem mul_eq_zero_iff (a k : Int) (h₁ : k > 0) : k * a = 0 ↔ a = 0 := by
  conv => lhs; rw [← Int.mul_zero k]
  apply Int.mul_eq_mul_left_iff
  exact Int.ne_of_gt h₁

theorem norm_eq_coeff' (ctx : Context) (p p' : Poly) (k : Int) : p = p'.mul k → k > 0 → (p.denote ctx = 0 ↔ p'.denote ctx = 0) := by
  intro; subst p; intro h; simp [mul_eq_zero_iff, *]

def norm_eq_coeff_cert (lhs rhs : Expr) (p : Poly) (k : Int) : Bool :=
  (lhs.sub rhs).norm == p.mul k && k > 0

theorem norm_eq_coeff (ctx : Context) (lhs rhs : Expr) (p : Poly) (k : Int)
    : norm_eq_coeff_cert lhs rhs p k → (lhs.denote ctx = rhs.denote ctx) = (p.denote' ctx = 0) := by
  simp [norm_eq_coeff_cert]
  rw [norm_eq ctx lhs rhs (lhs.sub rhs).norm BEq.refl, Poly.denote'_eq_denote]
  apply norm_eq_coeff'

private theorem mul_le_zero_iff (a k : Int) (h₁ : k > 0) : k * a ≤ 0 ↔ a ≤ 0 := by
  constructor
  · intro h
    rw [← Int.mul_zero k] at h
    exact Int.le_of_mul_le_mul_left h h₁
  · intro h
    replace h := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt h₁)
    simp at h; assumption

private theorem norm_le_coeff' (ctx : Context) (p p' : Poly) (k : Int) : p = p'.mul k → k > 0 → (p.denote ctx ≤ 0 ↔ p'.denote ctx ≤ 0) := by
  simp [norm_eq_coeff_cert]
  intro; subst p; intro h; simp [mul_le_zero_iff, *]

theorem norm_le_coeff (ctx : Context) (lhs rhs : Expr) (p : Poly) (k : Int)
    : norm_eq_coeff_cert lhs rhs p k → (lhs.denote ctx ≤ rhs.denote ctx) = (p.denote' ctx ≤ 0) := by
  simp [norm_eq_coeff_cert]
  rw [norm_le ctx lhs rhs (lhs.sub rhs).norm BEq.refl, Poly.denote'_eq_denote]
  apply norm_le_coeff'

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

private theorem eq_of_norm_eq_of_divCoeffs {ctx : Context} {p₁ p₂ : Poly} {k : Int}
    : k > 0 → p₁.divCoeffs k → p₂ = p₁.div k → (p₁.denote ctx ≤ 0 ↔ p₂.denote ctx ≤ 0) := by
  intro h₀ h₁ h₂
  have hz : k ≠ 0 := Int.ne_of_gt h₀
  replace h₁ := Poly.denote_div_eq_of_divCoeffs ctx p₁ k h₁
  replace h₂ := congrArg (Poly.denote ctx) h₂
  simp at h₂
  rw [h₂, ← h₁]; clear h₁ h₂
  apply mul_add_cmod_le_iff
  assumption

def norm_le_coeff_tight_cert (lhs rhs : Expr) (p : Poly) (k : Int) : Bool :=
  let p' := lhs.sub rhs |>.norm
  k > 0 && (p'.divCoeffs k && p == p'.div k)

theorem norm_le_coeff_tight (ctx : Context) (lhs rhs : Expr) (p : Poly) (k : Int)
    : norm_le_coeff_tight_cert lhs rhs p k → (lhs.denote ctx ≤ rhs.denote ctx) = (p.denote' ctx ≤ 0) := by
  simp [norm_le_coeff_tight_cert]
  rw [norm_le ctx lhs rhs (lhs.sub rhs).norm BEq.refl, Poly.denote'_eq_denote]
  apply eq_of_norm_eq_of_divCoeffs

def Poly.isUnsatEq (p : Poly) : Bool :=
  match p with
  | .num k => k != 0
  | _ => false

def Poly.isValidEq (p : Poly) : Bool :=
  match p with
  | .num k => k == 0
  | _ => false

theorem eq_eq_false (ctx : Context) (lhs rhs : Expr) : (lhs.sub rhs).norm.isUnsatEq → (lhs.denote ctx = rhs.denote ctx) = False := by
  simp [Poly.isUnsatEq] <;> split <;> simp
  next p k h =>
    intro h'
    replace h := congrArg (Poly.denote ctx) h
    simp at h
    rw [← Int.sub_eq_zero, h]
    assumption

theorem eq_eq_true (ctx : Context) (lhs rhs : Expr) : (lhs.sub rhs).norm.isValidEq → (lhs.denote ctx = rhs.denote ctx) = True := by
  simp [Poly.isValidEq] <;> split <;> simp
  next p k h =>
    intro h'
    replace h := congrArg (Poly.denote ctx) h
    simp at h
    rw [← Int.sub_eq_zero, h]
    assumption

def Poly.isUnsatLe (p : Poly) : Bool :=
  match p with
  | .num k => k > 0
  | _ => false

def Poly.isValidLe (p : Poly) : Bool :=
  match p with
  | .num k => k ≤ 0
  | _ => false

theorem le_eq_false (ctx : Context) (lhs rhs : Expr) : (lhs.sub rhs).norm.isUnsatLe → (lhs.denote ctx ≤ rhs.denote ctx) = False := by
  simp [Poly.isUnsatLe] <;> split <;> simp
  next p k h =>
    intro h'
    replace h := congrArg (Poly.denote ctx) h
    simp at h
    replace h := congrArg (Expr.denote ctx rhs + ·) h
    simp at h
    rw [Int.add_comm, Int.sub_add_cancel] at h
    rw [h]; clear h
    intro h
    conv at h => rhs; rw [← Int.zero_add (Expr.denote ctx rhs)]
    rw [Int.add_le_add_iff_right] at h
    replace h := Int.lt_of_lt_of_le h' h
    contradiction

theorem le_eq_true (ctx : Context) (lhs rhs : Expr) : (lhs.sub rhs).norm.isValidLe → (lhs.denote ctx ≤ rhs.denote ctx) = True := by
  simp [Poly.isValidLe] <;> split <;> simp
  next p k h =>
    intro h'
    replace h := congrArg (Poly.denote ctx) h
    simp at h
    replace h := congrArg (Expr.denote ctx rhs + ·) h
    simp at h
    rw [Int.add_comm, Int.sub_add_cancel] at h
    rw [h]; clear h; simp
    conv => rhs; rw [← Int.zero_add (Expr.denote ctx rhs)]
    rw [Int.add_le_add_iff_right]; assumption

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

private theorem poly_eq_zero_eq_false (ctx : Context) {p : Poly} {k : Int} : p.divCoeffs k → k > 0 → cmod p.getConst k < 0 → (p.denote ctx = 0) = False := by
  simp
  intro h₁ h₂ h₃ h
  have hnz : k ≠ 0 := by intro h; rw [h] at h₂; contradiction
  have := Poly.denote_div_eq_of_divCoeffs ctx p k h₁
  rw [h] at this
  have low := cmod_gt_of_pos p.getConst h₂
  have high := h₃
  exact contra h₂ low high this

def unsatEqDivCoeffCert (lhs rhs : Expr) (k : Int) : Bool :=
  let p := (lhs.sub rhs).norm
  p.divCoeffs k && k > 0 && cmod p.getConst k < 0

theorem eq_eq_false_of_divCoeff (ctx : Context) (lhs rhs : Expr) (k : Int) : unsatEqDivCoeffCert lhs rhs k → (lhs.denote ctx = rhs.denote ctx) = False := by
  simp [unsatEqDivCoeffCert]
  intro h₁ h₂ h₃
  have h := poly_eq_zero_eq_false ctx h₁ h₂ h₃; clear h₁ h₂ h₃
  simp at h
  intro h'
  simp [h'] at h

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

def Poly.isUnsatDvd (k : Int) (p : Poly) : Bool :=
  p.getConst % p.gcdCoeffs k != 0

private theorem not_dvd_of_not_mod_zero {a b : Int} (h : ¬ b % a = 0) : ¬ a ∣ b := by
  intro h; have := Int.emod_eq_zero_of_dvd h; contradiction

private theorem dvd_eq_false' (ctx : Context) (k : Int) (p : Poly) : p.isUnsatDvd k → (k ∣ p.denote' ctx) = False := by
  simp [Poly.isUnsatDvd]
  intro h₁ h₂
  have := Poly.gcd_dvd_const h₂
  have := not_dvd_of_not_mod_zero h₁
  contradiction

theorem dvd_unsat (ctx : Context) (k : Int) (p : Poly) : p.isUnsatDvd k → k ∣ p.denote' ctx → False := by
  intro h₁
  rw [dvd_eq_false' ctx _ _ h₁]
  intro; contradiction

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

theorem norm_dvd (ctx : Context) (k : Int) (e : Expr) (p : Poly) : e.norm == p → (k ∣ e.denote ctx) = (k ∣ p.denote' ctx) := by
  simp; intro h; simp [← h]

theorem dvd_eq_false (ctx : Context) (k : Int) (e : Expr) (h : e.norm.isUnsatDvd k) : (k ∣ e.denote ctx) = False := by
  rw [norm_dvd ctx k e e.norm BEq.refl]
  apply dvd_eq_false' ctx k e.norm h

def dvd_coeff_cert (k₁ : Int) (p₁ : Poly) (k₂ : Int) (p₂ : Poly) (k : Int) : Bool :=
  k != 0 && (k₁ == k*k₂ && p₁ == p₂.mul k)

def norm_dvd_gcd_cert (k₁ : Int) (e₁ : Expr) (k₂ : Int) (p₂ : Poly) (k : Int) : Bool :=
  dvd_coeff_cert k₁ e₁.norm k₂ p₂ k

theorem norm_dvd_gcd (ctx : Context) (k₁ : Int) (e₁ : Expr) (k₂ : Int) (p₂ : Poly) (g : Int)
    : norm_dvd_gcd_cert k₁ e₁ k₂ p₂ g → (k₁ ∣ e₁.denote ctx) = (k₂ ∣ p₂.denote' ctx) := by
  simp [norm_dvd_gcd_cert, dvd_coeff_cert]
  intro h₁ h₂ h₃
  replace h₃ := congrArg (Poly.denote ctx) h₃
  simp at h₃
  simp [*]

theorem dvd_coeff (ctx : Context) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (p₂ : Poly) (g : Int)
    : dvd_coeff_cert k₁ p₁ k₂ p₂ g → k₁ ∣ p₁.denote' ctx → k₂ ∣ p₂.denote' ctx := by
  simp [dvd_coeff_cert]
  intro h₁ h₂ h₃
  replace h₃ := congrArg (Poly.denote ctx) h₃
  simp at h₃
  simp [*]

private theorem dvd_gcd_of_dvd (d a x p : Int) (h : d ∣ a * x + p) : gcd d a ∣ p := by
  rcases h with ⟨k, h⟩
  simp [Int.Linear.gcd]
  replace h := congrArg (· - a*x) h
  simp at h
  rcases @Int.gcd_dvd_left d a with ⟨k₁, h₁⟩
  rcases @Int.gcd_dvd_right d a with ⟨k₂, h₂⟩
  conv at h => enter [2, 1]; rw [h₁]
  conv at h => enter [2, 2]; rw [h₂]
  rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_sub] at h
  exists k₁ * k - k₂ * x

def dvd_elim_cert (k₁ : Int) (p₁ : Poly) (k₂ : Int) (p₂ : Poly) : Bool :=
  match p₁ with
  | .add a _ p => k₂ == gcd k₁ a && p₂ == p
  | _ => false

theorem dvd_elim (ctx : Context) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (p₂ : Poly)
    : dvd_elim_cert k₁ p₁ k₂ p₂ → k₁ ∣ p₁.denote' ctx → k₂ ∣ p₂.denote' ctx := by
  rcases p₁ <;> simp [dvd_elim_cert]
  next a _ p =>
  intro _ _; subst k₂ p₂
  rw [Int.add_comm]
  apply dvd_gcd_of_dvd

private theorem dvd_solve_combine' {x : Int} {d₁ a₁ p₁ : Int} {d₂ a₂ p₂ : Int} {α β d : Int}
   (h : α*a₁*d₂ + β*a₂*d₁ = d)
   (h₁ : d₁ ∣ a₁*x + p₁)
   (h₂ : d₂ ∣ a₂*x + p₂)
   : d₁*d₂ ∣ d*x + α*d₂*p₁ + β*d₁*p₂ := by
 rcases h₁ with ⟨k₁, h₁⟩
 replace h₁ : α*a₁*d₂*x + α*d₂*p₁ = d₁*d₂*(α*k₁) := by
   have ac₁ : d₁*d₂*(α*k₁) = α*d₂*(d₁*k₁) := by ac_rfl
   have ac₂ : α * a₁ * d₂ * x = α * d₂ * (a₁ * x) := by ac_rfl
   rw [ac₁, ← h₁, Int.mul_add, ac₂]
 rcases h₂ with ⟨k₂, h₂⟩
 replace h₂ : β*a₂*d₁*x + β*d₁*p₂ = d₁*d₂*(β*k₂) := by
   have ac₁ : d₁*d₂*(β*k₂) = β*d₁*(d₂*k₂) := by ac_rfl
   have ac₂ : β * a₂ * d₁ * x = β * d₁ * (a₂ * x) := by ac_rfl
   rw [ac₁, ←h₂, Int.mul_add, ac₂]
 replace h₁ : d₁*d₂ ∣ α*a₁*d₂*x + α*d₂*p₁ := ⟨α*k₁, h₁⟩
 replace h₂ : d₁*d₂ ∣ β*a₂*d₁*x + β*d₁*p₂ := ⟨β*k₂, h₂⟩
 have h' := Int.dvd_add h₁ h₂; clear h₁ h₂ k₁ k₂
 replace h : d*x = α*a₁*d₂*x + β*a₂*d₁*x := by
   rw [←h, Int.add_mul]
 have ac :
   α * a₁ * d₂ * x + α * d₂ * p₁ + (β * a₂ * d₁ * x + β * d₁ * p₂)
   =
   α * a₁ * d₂ * x + β * a₂ * d₁ * x + α * d₂ * p₁ + β * d₁ * p₂ := by ac_rfl
 rw [h, ←ac]
 assumption

private theorem dvd_solve_elim' {x : Int} {d₁ a₁ p₁ : Int} {d₂ a₂ p₂ : Int} {d : Int}
   (h : d = Int.gcd (a₁*d₂) (a₂*d₁))
   (h₁ : d₁ ∣ a₁*x + p₁)
   (h₂ : d₂ ∣ a₂*x + p₂)
   : d ∣ a₂*p₁ - a₁*p₂ := by
 rcases h₁ with ⟨k₁, h₁⟩
 rcases h₂ with ⟨k₂, h₂⟩
 have h₃ : d ∣ a₁*d₂ := by
  rw [h]; apply Int.gcd_dvd_left
 have h₄ : d ∣ a₂*d₁ := by
  rw [h]; apply Int.gcd_dvd_right
 rcases h₃ with ⟨k₃, h₃⟩
 rcases h₄ with ⟨k₄, h₄⟩
 have : a₂*p₁ - a₁*p₂ = a₂*d₁*k₁ - a₁*d₂*k₂ := by
   have ac₁ : a₂*d₁*k₁ = a₂*(d₁*k₁) := by ac_rfl
   have ac₂ : a₁*d₂*k₂ = a₁*(d₂*k₂) := by ac_rfl
   have ac₃ : a₁*(a₂*x) = a₂*(a₁*x) := by ac_rfl
   rw [ac₁, ac₂, ←h₁, ←h₂, Int.mul_add, Int.mul_add, ac₃, ←Int.sub_sub, Int.add_comm, Int.add_sub_assoc]
   simp
 rw [h₃, h₄, Int.mul_assoc, Int.mul_assoc, ←Int.mul_sub] at this
 exact ⟨k₄ * k₁ - k₃ * k₂, this⟩

def dvd_solve_combine_cert (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly) (g α β : Int) : Bool :=
  match p₁, p₂ with
  | .add a₁ x₁ p₁, .add a₂ x₂ p₂ =>
    x₁ == x₂ &&
    (g == α*a₁*d₂ + β*a₂*d₁ &&
    (d == d₁*d₂ &&
     p == .add g x₁ (p₁.mul (α*d₂) |>.combine (p₂.mul (β*d₁)))))
  | _, _ => false

theorem dvd_solve_combine (ctx : Context) (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly) (g α β : Int)
    : dvd_solve_combine_cert d₁ p₁ d₂ p₂ d p g α β → d₁ ∣ p₁.denote' ctx → d₂ ∣ p₂.denote' ctx → d ∣ p.denote' ctx := by
  simp [dvd_solve_combine_cert]
  split <;> simp
  next a₁ x₁ p₁ a₂ x₂ p₂ =>
  intro _ hg hd hp; subst x₁ p
  simp [Poly.denote'_add]
  intro h₁ h₂
  rw [Int.add_comm] at h₁ h₂
  rw [Int.add_comm _ (g * x₂.denote ctx), Int.add_left_comm, ← Int.add_assoc, hd]
  exact dvd_solve_combine' hg.symm h₁ h₂

def dvd_solve_elim_cert (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly) : Bool :=
  match p₁, p₂ with
  | .add a₁ x₁ p₁, .add a₂ x₂ p₂ =>
    x₁ == x₂ &&
    (d == Int.gcd (a₁*d₂) (a₂*d₁) &&
     p == (p₁.mul a₂ |>.combine (p₂.mul (- a₁))))
  | _, _ => false

theorem dvd_solve_elim (ctx : Context) (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly)
    : dvd_solve_elim_cert d₁ p₁ d₂ p₂ d p → d₁ ∣ p₁.denote' ctx → d₂ ∣ p₂.denote' ctx → d ∣ p.denote' ctx := by
  simp [dvd_solve_elim_cert]
  split <;> simp
  next a₁ x₁ p₁ a₂ x₂ p₂ =>
  intro _ hd _; subst x₁ p; simp
  intro h₁ h₂
  rw [Int.add_comm] at h₁ h₂
  rw [← Int.sub_eq_add_neg]
  exact dvd_solve_elim' hd h₁ h₂

theorem dvd_norm (ctx : Context) (d : Int) (p₁ p₂ : Poly) : p₁.norm == p₂ → d ∣ p₁.denote' ctx → d ∣ p₂.denote' ctx := by
  simp
  intro; subst p₂
  intro h₁
  simp [Poly.denote_norm ctx p₁, h₁]

theorem le_norm (ctx : Context) (p₁ p₂ : Poly) (h : p₁.norm == p₂) : p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 := by
  simp at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  simp [*]

def le_coeff_cert (p₁ p₂ : Poly) (k : Int) : Bool :=
  k > 0 && (p₁.divCoeffs k && p₂ == p₁.div k)

theorem le_coeff (ctx : Context) (p₁ p₂ : Poly) (k : Int) : le_coeff_cert p₁ p₂ k → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 := by
  simp [le_coeff_cert]
  intro h₁ h₂ h₃
  exact eq_of_norm_eq_of_divCoeffs h₁ h₂ h₃ |>.mp

def le_neg_cert (p₁ p₂ : Poly) : Bool :=
  p₂ == (p₁.mul (-1) |>.addConst 1)

theorem le_neg (ctx : Context) (p₁ p₂ : Poly) : le_neg_cert p₁ p₂ → ¬ p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 := by
  simp [le_neg_cert]
  intro; subst p₂; simp; intro h
  replace h : _ + 1 ≤ -0 := Int.neg_lt_neg <| Int.lt_of_not_ge h
  simp at h
  exact h

def Poly.leadCoeff (p : Poly) : Int :=
  match p with
  | .add a _ _ => a
  | _ => 1

def le_combine_cert (p₁ p₂ p₃ : Poly) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  p₃ == (p₁.mul a₂ |>.combine (p₂.mul a₁))

theorem le_combine (ctx : Context) (p₁ p₂ p₃ : Poly)
    : le_combine_cert p₁ p₂ p₃ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [le_combine_cert]
  intro; subst p₃
  intro h₁ h₂; simp
  rw [← Int.add_zero 0]
  apply Int.add_le_add
  · rw [← Int.zero_mul (Poly.denote ctx p₂)]; apply Int.mul_le_mul_of_nonpos_right <;> simp [*]
  · rw [← Int.zero_mul (Poly.denote ctx p₁)]; apply Int.mul_le_mul_of_nonpos_right <;> simp [*]

theorem le_unsat (ctx : Context) (p : Poly) : p.isUnsatLe → p.denote' ctx ≤ 0 → False := by
  simp [Poly.isUnsatLe]; split <;> simp
  intro h₁ h₂
  have := Int.lt_of_le_of_lt h₂ h₁
  simp at this

def Poly.coeff (p : Poly) (x : Var) : Int :=
  match p with
  | .add a y p => bif x == y then a else coeff p x
  | .num _ => 0

private theorem eq_add_coeff_insert (ctx : Context) (p : Poly) (x : Var) : p.denote ctx = (p.coeff x) * (x.denote ctx) + (p.insert (-p.coeff x) x).denote ctx := by
  simp; rw [← Int.add_assoc, Int.add_neg_cancel_right]

private theorem dvd_of_eq' {a x p : Int} : a*x + p = 0 → a ∣ p := by
  intro h
  replace h := Int.neg_eq_of_add_eq_zero h
  rw [Int.mul_comm, ← Int.neg_mul, Eq.comm, Int.mul_comm] at h
  exact ⟨-x, h⟩

def dvd_of_eq_cert (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) : Bool :=
  d₂ == p₁.coeff x && p₂ == p₁.insert (-d₂) x

theorem dvd_of_eq (ctx : Context) (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly)
    : dvd_of_eq_cert x p₁ d₂ p₂ → p₁.denote' ctx = 0 → d₂ ∣ p₂.denote' ctx := by
  simp [dvd_of_eq_cert]
  intro h₁ h₂
  have h := eq_add_coeff_insert ctx p₁ x
  rw [← h₁, ← h₂] at h
  rw [h]
  apply dvd_of_eq'

private theorem eq_dvd_subst' {a x p d b q : Int} : a*x + p = 0 → d ∣ b*x + q → a*d ∣ a*q - b*p := by
  intro h₁ ⟨z, h₂⟩
  have h : a*q - b*p = a*(b*x + q) - b*(a*x+p) := by
    conv => rhs; rw [Int.sub_eq_add_neg]; rhs; rw [Int.mul_add, Int.neg_add]
    rw [Int.mul_add, ←Int.add_assoc, Int.mul_left_comm a b x]
    rw [Int.add_comm (b*(a*x)), Int.add_neg_cancel_right, Int.sub_eq_add_neg]
  rw [h₁, h₂] at h
  simp at h
  rw [← Int.mul_assoc] at h
  exact ⟨z, h⟩

def eq_dvd_subst_cert (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d₃ : Int) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  let p := p₁.insert (-a) x
  let q := p₂.insert (-b) x
  d₃ == a * d₂ &&
  p₃ == (q.mul a |>.combine (p.mul (-b)))

theorem eq_dvd_subst (ctx : Context) (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d₃ : Int) (p₃ : Poly)
    : eq_dvd_subst_cert x p₁ d₂ p₂ d₃ p₃ → p₁.denote' ctx = 0 → d₂ ∣ p₂.denote' ctx → d₃ ∣ p₃.denote' ctx := by
  simp [eq_dvd_subst_cert]
  have eq₁ := eq_add_coeff_insert ctx p₁ x
  have eq₂ := eq_add_coeff_insert ctx p₂ x
  revert eq₁ eq₂
  generalize p₁.coeff x = a
  generalize p₂.coeff x = b
  generalize p₁.insert (-a) x = p
  generalize p₂.insert (-b) x = q
  intro eq₁; simp [eq₁]; clear eq₁
  intro eq₂; simp [eq₂]; clear eq₂
  intro; subst d₃
  intro; subst p₃
  intro h₁ h₂
  rw [Int.add_comm] at h₁ h₂
  have := eq_dvd_subst' h₁ h₂
  rw [Int.sub_eq_add_neg, Int.add_comm] at this
  simp [this]

private theorem eq_eq_subst' {a x p b q : Int} : a*x + p = 0 → b*x + q = 0 → b*p - a*q = 0 := by
  intro h₁ h₂
  replace h₁ := congrArg (b*·) h₁; simp at h₁
  replace h₂ := congrArg ((-a)*.) h₂; simp at h₂
  rw [Int.add_comm] at h₁
  replace h₁ := Int.neg_eq_of_add_eq_zero h₁
  rw [← h₁]; clear h₁
  replace h₂ := Int.neg_eq_of_add_eq_zero h₂; simp at h₂
  rw [h₂]; clear h₂
  rw [Int.mul_left_comm]
  simp

def eq_eq_subst_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  let p := p₁.insert (-a) x
  let q := p₂.insert (-b) x
  p₃ == (p.mul b |>.combine (q.mul (-a)))

theorem eq_eq_subst (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_eq_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 → p₃.denote' ctx = 0 := by
  simp [eq_eq_subst_cert]
  have eq₁ := eq_add_coeff_insert ctx p₁ x
  have eq₂ := eq_add_coeff_insert ctx p₂ x
  revert eq₁ eq₂
  generalize p₁.coeff x = a
  generalize p₂.coeff x = b
  generalize p₁.insert (-a) x = p
  generalize p₂.insert (-b) x = q
  intro eq₁; simp [eq₁]; clear eq₁
  intro eq₂; simp [eq₂]; clear eq₂
  intro; subst p₃
  intro h₁ h₂
  rw [Int.add_comm] at h₁ h₂
  have := eq_eq_subst' h₁ h₂
  rw [Int.sub_eq_add_neg] at this
  simp [this]

private theorem eq_le_subst_nonneg' {a x p b q : Int} : a ≥ 0 → a*x + p = 0 → b*x + q ≤ 0 → a*q - b*p ≤ 0 := by
  intro h h₁ h₂
  replace h₁ := congrArg ((-b)*·) h₁; simp at h₁
  rw [Int.add_comm, Int.mul_left_comm] at h₁
  replace h₁ := Int.neg_eq_of_add_eq_zero h₁; simp at h₁
  replace h₂ := Int.mul_le_mul_of_nonneg_left h₂ h
  rw [Int.mul_add, h₁] at h₂; clear h₁
  simp at h₂
  rw [Int.sub_eq_add_neg]
  assumption

def eq_le_subst_nonneg_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  let p := p₁.insert (-a) x
  let q := p₂.insert (-b) x
  a ≥ 0 && p₃ == (q.mul a |>.combine (p.mul (-b)))

theorem eq_le_subst_nonneg (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_le_subst_nonneg_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [eq_le_subst_nonneg_cert]
  have eq₁ := eq_add_coeff_insert ctx p₁ x
  have eq₂ := eq_add_coeff_insert ctx p₂ x
  revert eq₁ eq₂
  generalize p₁.coeff x = a
  generalize p₂.coeff x = b
  generalize p₁.insert (-a) x = p
  generalize p₂.insert (-b) x = q
  intro eq₁; simp [eq₁]; clear eq₁
  intro eq₂; simp [eq₂]; clear eq₂
  intro h
  intro; subst p₃
  intro h₁ h₂
  rw [Int.add_comm] at h₁ h₂
  have := eq_le_subst_nonneg' h h₁ h₂
  rw [Int.sub_eq_add_neg, Int.add_comm] at this
  simp [this]

private theorem eq_le_subst_nonpos' {a x p b q : Int} : a ≤ 0 → a*x + p = 0 → b*x + q ≤ 0 → b*p - a*q ≤ 0 := by
  intro h h₁ h₂
  replace h₁ := congrArg (b*·) h₁; simp at h₁
  rw [Int.add_comm, Int.mul_left_comm] at h₁
  replace h₁ := Int.neg_eq_of_add_eq_zero h₁; simp at h₁
  replace h : (-a) ≥ 0 := by
    have := Int.neg_le_neg h
    simp at this
    exact this
  replace h₂ := Int.mul_le_mul_of_nonneg_left h₂ h; simp at h₂; clear h
  rw [h₁] at h₂
  rw [Int.add_comm, ←Int.sub_eq_add_neg] at h₂
  assumption

def eq_le_subst_nonpos_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  let p := p₁.insert (-a) x
  let q := p₂.insert (-b) x
  a ≤ 0 && p₃ == (p.mul b |>.combine (q.mul (-a)))

theorem eq_le_subst_nonpos (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_le_subst_nonpos_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [eq_le_subst_nonpos_cert]
  have eq₁ := eq_add_coeff_insert ctx p₁ x
  have eq₂ := eq_add_coeff_insert ctx p₂ x
  revert eq₁ eq₂
  generalize p₁.coeff x = a
  generalize p₂.coeff x = b
  generalize p₁.insert (-a) x = p
  generalize p₂.insert (-b) x = q
  intro eq₁; simp [eq₁]; clear eq₁
  intro eq₂; simp [eq₂]; clear eq₂
  intro h
  intro; subst p₃
  intro h₁ h₂
  rw [Int.add_comm] at h₁ h₂
  have := eq_le_subst_nonpos' h h₁ h₂
  rw [Int.sub_eq_add_neg] at this
  simp [this]

end Int.Linear

theorem Int.not_le_eq (a b : Int) : (¬a ≤ b) = (b + 1 ≤ a) := by
  apply propext; constructor
  · intro h; exact Int.add_one_le_of_lt (Int.lt_of_not_ge h)
  · exact Int.not_le_of_gt

theorem Int.not_ge_eq (a b : Int) : (¬a ≥ b) = (a + 1 ≤ b) := by
  apply Int.not_le_eq

theorem Int.not_lt_eq (a b : Int) : (¬a < b) = (b ≤ a) := by
  apply propext; constructor
  · intro h; simp [Int.not_lt] at h; assumption
  · intro h; apply Int.not_le_of_gt; simp [Int.lt_add_one_iff, *]

theorem Int.not_gt_eq (a b : Int) : (¬a > b) = (a ≤ b) := by
  apply Int.not_lt_eq
