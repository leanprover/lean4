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
import Init.Data.Int.Cooper
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
  simp [Int.neg_emod_eq_sub_emod, ← this, Eq.comm]

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

attribute [-simp] Int.not_le in
theorem le_eq_false (ctx : Context) (lhs rhs : Expr) : (lhs.sub rhs).norm.isUnsatLe → (lhs.denote ctx ≤ rhs.denote ctx) = False := by
  simp only [Poly.isUnsatLe] <;> split <;> simp
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
  replace h : _ + 1 ≤ -0 := Int.neg_lt_neg h
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

def le_combine_coeff_cert (p₁ p₂ p₃ : Poly) (k : Int) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  let p  := p₁.mul a₂ |>.combine (p₂.mul a₁)
  k > 0 && (p.divCoeffs k && p₃ == p.div k)

theorem le_combine_coeff (ctx : Context) (p₁ p₂ p₃ : Poly) (k : Int)
    : le_combine_coeff_cert p₁ p₂ p₃ k → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp only [le_combine_coeff_cert, gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_imp]
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  generalize h : (p₁.mul a₂ |>.combine (p₂.mul a₁)) = p
  intro h₁ h₂ h₃ h₄ h₅
  have := le_combine ctx p₁ p₂ p
  simp only [le_combine_cert, beq_iff_eq] at this
  have aux₁ := this h.symm h₄ h₅
  have := le_coeff ctx p p₃ k
  simp only [le_coeff_cert, gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_imp] at this
  exact this h₁ h₂ h₃ aux₁

theorem le_unsat (ctx : Context) (p : Poly) : p.isUnsatLe → p.denote' ctx ≤ 0 → False := by
  simp [Poly.isUnsatLe]; split <;> simp

theorem eq_norm (ctx : Context) (p₁ p₂ : Poly) (h : p₁.norm == p₂) : p₁.denote' ctx = 0 → p₂.denote' ctx = 0 := by
  simp at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  simp [*]

def eq_coeff_cert (p p' : Poly) (k : Int) : Bool :=
  p == p'.mul k && k > 0

theorem eq_coeff (ctx : Context) (p p' : Poly) (k : Int) : eq_coeff_cert p p' k → p.denote' ctx = 0 → p'.denote' ctx = 0 := by
  simp [eq_coeff_cert]
  intro _ _; simp [mul_eq_zero_iff, *]

theorem eq_unsat (ctx : Context) (p : Poly) : p.isUnsatEq → p.denote' ctx = 0 → False := by
  simp [Poly.isUnsatEq] <;> split <;> simp

def eq_unsat_coeff_cert (p : Poly) (k : Int) : Bool :=
  p.divCoeffs k && k > 0 && cmod p.getConst k < 0

theorem eq_unsat_coeff (ctx : Context) (p : Poly) (k : Int) : eq_unsat_coeff_cert p k → p.denote' ctx = 0 → False := by
  simp [eq_unsat_coeff_cert]
  intro h₁ h₂ h₃
  have h := poly_eq_zero_eq_false ctx h₁ h₂ h₃; clear h₁ h₂ h₃
  simp [h]

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

private def abs (x : Int) : Int :=
  Int.ofNat x.natAbs

private theorem abs_dvd {a p : Int} (h : a ∣ p) : abs a ∣ p := by
  cases a <;> simp [abs]
  · simp at h; assumption
  · simp [Int.negSucc_eq] at h; assumption

def dvd_of_eq_cert (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) : Bool :=
  let a := p₁.coeff x
  d₂ == abs a && p₂ == p₁.insert (-a) x

theorem dvd_of_eq (ctx : Context) (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly)
    : dvd_of_eq_cert x p₁ d₂ p₂ → p₁.denote' ctx = 0 → d₂ ∣ p₂.denote' ctx := by
  simp [dvd_of_eq_cert]
  intro h₁ h₂
  have h := eq_add_coeff_insert ctx p₁ x
  rw [← h₂] at h
  rw [h, h₁]
  intro h₃
  apply abs_dvd
  apply dvd_of_eq' h₃

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
  d₃ == abs (a * d₂) &&
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
  apply abs_dvd
  simp [this]

def eq_eq_subst_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  p₃ == (p₁.mul b |>.combine (p₂.mul (-a)))

theorem eq_eq_subst (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_eq_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 → p₃.denote' ctx = 0 := by
  simp [eq_eq_subst_cert]
  intro; subst p₃
  intro h₁ h₂
  simp [*]

def eq_le_subst_nonneg_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  a ≥ 0 && p₃ == (p₂.mul a |>.combine (p₁.mul (-b)))

theorem eq_le_subst_nonneg (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_le_subst_nonneg_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [eq_le_subst_nonneg_cert]
  intro h
  intro; subst p₃
  intro h₁ h₂
  replace h₂ := Int.mul_le_mul_of_nonneg_left h₂ h
  simp at h₂
  simp [*]

def eq_le_subst_nonpos_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  a ≤ 0 && p₃ == (p₁.mul b |>.combine (p₂.mul (-a)))

theorem eq_le_subst_nonpos (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_le_subst_nonpos_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [eq_le_subst_nonpos_cert]
  intro h
  intro; subst p₃
  intro h₁ h₂
  simp [*]
  replace h₂ := Int.mul_le_mul_of_nonpos_left h₂ h; simp at h₂; clear h
  rw [← Int.neg_zero]
  apply Int.neg_le_neg
  rw [Int.mul_comm]
  assumption

def eq_of_core_cert (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  p₃ == p₁.combine (p₂.mul (-1))

theorem eq_of_core (ctx : Context) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_of_core_cert p₁ p₂ p₃ → p₁.denote' ctx = p₂.denote' ctx → p₃.denote' ctx = 0 := by
  simp [eq_of_core_cert]
  intro; subst p₃; simp
  intro h; rw [h, ←Int.sub_eq_add_neg, Int.sub_self]

def Poly.isUnsatDiseq (p : Poly) : Bool :=
  match p with
  | .num 0 => true
  | _ => false

theorem diseq_norm (ctx : Context) (p₁ p₂ : Poly) (h : p₁.norm == p₂) : p₁.denote' ctx ≠ 0 → p₂.denote' ctx ≠ 0 := by
  simp at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  simp [*]

theorem diseq_coeff (ctx : Context) (p p' : Poly) (k : Int) : eq_coeff_cert p p' k → p.denote' ctx ≠ 0 → p'.denote' ctx ≠ 0 := by
  simp [eq_coeff_cert]
  intro _ _; simp [mul_eq_zero_iff, *]

theorem diseq_neg (ctx : Context) (p p' : Poly) : p' == p.mul (-1) → p.denote' ctx ≠ 0 → p'.denote' ctx ≠ 0 := by
  simp; intro _ _; simp [mul_eq_zero_iff, *]

theorem diseq_unsat (ctx : Context) (p : Poly) : p.isUnsatDiseq → p.denote' ctx ≠ 0 → False := by
  simp [Poly.isUnsatDiseq] <;> split <;> simp

def diseq_eq_subst_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  a != 0 && p₃ == (p₁.mul b |>.combine (p₂.mul (-a)))

theorem eq_diseq_subst (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : diseq_eq_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≠ 0 → p₃.denote' ctx ≠ 0 := by
  simp [diseq_eq_subst_cert]
  intros _ _; subst p₃
  intro h₁ h₂
  simp [*]

theorem diseq_of_core (ctx : Context) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_of_core_cert p₁ p₂ p₃ → p₁.denote' ctx ≠ p₂.denote' ctx → p₃.denote' ctx ≠ 0 := by
  simp [eq_of_core_cert]
  intro; subst p₃; simp
  intro h; rw [← Int.sub_eq_zero] at h
  rw [←Int.sub_eq_add_neg]; assumption

def eq_of_le_ge_cert (p₁ p₂ : Poly) : Bool :=
  p₂ == p₁.mul (-1)

theorem eq_of_le_ge (ctx : Context) (p₁ : Poly) (p₂ : Poly)
    : eq_of_le_ge_cert p₁ p₂ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₁.denote' ctx = 0 := by
  simp [eq_of_le_ge_cert]
  intro; subst p₂; simp
  intro h₁ h₂
  replace h₂ := Int.neg_le_of_neg_le h₂; simp at h₂
  simp [Int.eq_iff_le_and_ge, *]

def le_of_le_diseq_cert (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  -- Remark: we can generate two different certificates in the future, and avoid the `||` in the certificate.
  (p₂ == p₁ || p₂ == p₁.mul (-1)) &&
  p₃ == p₁.addConst 1

theorem le_of_le_diseq (ctx : Context) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : le_of_le_diseq_cert p₁ p₂ p₃ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≠ 0 → p₃.denote' ctx ≤ 0 := by
  simp [le_of_le_diseq_cert]
  have (a : Int) : a ≤ 0 → ¬ a = 0 → 1 + a ≤ 0 := by
    intro h₁ h₂; cases (Int.lt_or_gt_of_ne h₂)
    next => apply Int.le_of_lt_add_one; rw [Int.add_comm, Int.add_lt_add_iff_right]; assumption
    next h => have := Int.lt_of_le_of_lt h₁ h; simp at this
  intro h; cases h <;> intro <;> subst p₂ p₃ <;> simp <;> apply this

def diseq_split_cert (p₁ p₂ p₃ : Poly) : Bool :=
  p₂ == p₁.addConst 1 &&
  p₃ == (p₁.mul (-1)).addConst 1

theorem diseq_split (ctx : Context) (p₁ p₂ p₃ : Poly)
    : diseq_split_cert p₁ p₂ p₃ → p₁.denote' ctx ≠ 0 → p₂.denote' ctx ≤ 0 ∨ p₃.denote' ctx ≤ 0 := by
  simp [diseq_split_cert]
  intro _ _; subst p₂ p₃; simp
  generalize p₁.denote ctx = p
  intro h; cases Int.lt_or_gt_of_ne h
  next h => have := Int.add_one_le_of_lt h; rw [Int.add_comm]; simp [*]
  next h => have := Int.add_one_le_of_lt (Int.neg_lt_neg h); simp at this; simp [*]

theorem diseq_split_resolve (ctx : Context) (p₁ p₂ p₃ : Poly)
    : diseq_split_cert p₁ p₂ p₃ → p₁.denote' ctx ≠ 0 → ¬p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  intro h₁ h₂ h₃
  exact (diseq_split ctx p₁ p₂ p₃ h₁ h₂).resolve_left h₃

def OrOver (n : Nat) (p : Nat → Prop) : Prop :=
  match n with
  | 0 => False
  | n+1 => p n ∨ OrOver n p

theorem orOver_one {p} : OrOver 1 p → p 0 := by simp [OrOver]

theorem orOver_resolve {n p} : OrOver (n+1) p → ¬ p n → OrOver n p := by
  intro h₁ h₂
  rw [OrOver] at h₁
  cases h₁
  · contradiction
  · assumption

def OrOver_cases_type (n : Nat) (p : Nat → Prop) : Prop :=
  match n with
  | 0 => p 0
  | n+1 => ¬ p (n+1) → OrOver_cases_type n p

theorem orOver_cases {n p} : OrOver (n+1) p → OrOver_cases_type n p := by
  induction n <;> simp [OrOver_cases_type]
  next => exact orOver_one
  next n ih => intro h₁ h₂; exact ih (orOver_resolve h₁ h₂)

private theorem orOver_of_p {i n p} (h₁ : i < n) (h₂ : p i) : OrOver n p := by
  induction n
  next => simp at h₁
  next n ih =>
    simp [OrOver]
    cases Nat.eq_or_lt_of_le <| Nat.le_of_lt_add_one h₁
    next h => subst i; exact Or.inl h₂
    next h => exact Or.inr (ih h)

private theorem orOver_of_exists {n p} : (∃ k, k < n ∧ p k) → OrOver n p := by
  intro ⟨k, h₁, h₂⟩
  apply orOver_of_p h₁ h₂

private theorem ofNat_toNat {a : Int} : a ≥ 0 → Int.ofNat a.toNat = a := by cases a <;> simp
private theorem cast_toNat {a : Int} : a ≥ 0 → a.toNat = a := by cases a <;> simp
private theorem ofNat_lt {a : Int} {n : Nat} : a ≥ 0 → a < Int.ofNat n → a.toNat < n := by cases a <;> simp
@[local simp] private theorem lcm_neg_left (a b : Int) : Int.lcm (-a) b = Int.lcm a b := by simp [Int.lcm]
@[local simp] private theorem lcm_neg_right (a b : Int) : Int.lcm a (-b) = Int.lcm a b := by simp [Int.lcm]
@[local simp] private theorem gcd_neg_left (a b : Int) : Int.gcd (-a) b = Int.gcd a b := by simp [Int.gcd]
@[local simp] private theorem gcd_neg_right (a b : Int) : Int.gcd a (-b) = Int.gcd a b := by simp [Int.gcd]
@[local simp] private theorem gcd_zero (a : Int) : Int.gcd a 0 = a.natAbs := by simp [Int.gcd]
@[local simp] private theorem lcm_one (a : Int) : Int.lcm a 1 = a.natAbs := by simp [Int.lcm]

private theorem cooper_dvd_left_core
    {a b c d s p q x : Int} (a_neg : a < 0) (b_pos : 0 < b) (d_pos : 0 < d)
    (h₁ : a * x + p ≤ 0)
    (h₂ : b * x + q ≤ 0)
    (h₃ : d ∣ c * x + s)
    : OrOver (Int.lcm a (a * d / Int.gcd (a * d) c)) fun k =>
        b * p + (-a) * q + b * k ≤ 0 ∧
        a ∣ p + k ∧
        a * d ∣ c * p + (-a) * s + c * k := by
  have a_pos' : 0 < -a := by apply Int.neg_pos_of_neg; assumption
  have h₁'    : p ≤ (-a)*x := by rw [Int.neg_mul, ← Lean.Omega.Int.add_le_zero_iff_le_neg']; assumption
  have h₂'    : b * x ≤ -q := by rw [← Lean.Omega.Int.add_le_zero_iff_le_neg', Int.add_comm]; assumption
  have ⟨k, h₁, h₂, h₃, h₄, h₅⟩ := Int.cooper_resolution_dvd_left a_pos' b_pos d_pos |>.mp ⟨x, h₁', h₂', h₃⟩
  rw [Int.neg_mul] at h₂
  simp only [Int.neg_mul, neg_gcd, lcm_neg_left, Int.mul_neg, Int.neg_neg, Int.neg_dvd] at *
  rw [Int.neg_ediv_of_dvd Int.gcd_dvd_left] at h₂
  simp only [lcm_neg_right] at h₂
  have : c * k + c * p + -(a * s) = c * p + -(a * s) + c * k := by ac_rfl
  rw [this] at h₅; clear this
  rw [← ofNat_toNat h₁] at h₃ h₄ h₅
  rw [Int.add_comm] at h₄
  have := ofNat_lt h₁ h₂
  apply orOver_of_exists
  replace h₃ := Int.add_le_add_right h₃ (-(a*q)); rw [Int.add_right_neg] at h₃
  have : b * Int.ofNat k.toNat + b * p + -(a * q) = b * p + -(a * q) + b * Int.ofNat k.toNat := by ac_rfl
  rw [this] at h₃
  exists k.toNat

def cooper_dvd_left_cert (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat) : Bool :=
  p₁.casesOn (fun _ => false) fun a x _ =>
  p₂.casesOn (fun _ => false) fun b y _ =>
  p₃.casesOn (fun _ => false) fun c z _ =>
   .and (x == y) <| .and (x == z) <|
   .and (a < 0)  <| .and (b > 0)  <|
   .and (d > 0)  <| n == Int.lcm a (a * d / Int.gcd (a * d) c)

def Poly.tail (p : Poly) : Poly :=
  match p with
  | .add _ _ p => p
  | _ => p

def cooper_dvd_left_split (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) : Prop :=
  let p  := p₁.tail
  let q  := p₂.tail
  let s  := p₃.tail
  let a  := p₁.leadCoeff
  let b  := p₂.leadCoeff
  let c  := p₃.leadCoeff
  let p₁ := p.mul b |>.combine (q.mul (-a))
  let p₂ := p.mul c |>.combine (s.mul (-a))
  (p₁.addConst (b*k)).denote' ctx ≤ 0
  ∧ a ∣ (p.addConst k).denote' ctx
  ∧ a*d ∣ (p₂.addConst (c*k)).denote' ctx

private theorem denote'_mul_combine_mul_addConst_eq (ctx : Context) (p q : Poly) (a b c : Int)
    : ((p.mul b |>.combine (q.mul a)).addConst c).denote' ctx = b*p.denote ctx + a*q.denote ctx + c := by
  simp

private theorem denote'_addConst_eq (ctx : Context) (p : Poly) (a : Int)
    : (p.addConst a).denote' ctx = p.denote ctx + a := by
  simp

theorem cooper_dvd_left (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat)
    : cooper_dvd_left_cert p₁ p₂ p₃ d n
      → p₁.denote' ctx ≤ 0
      → p₂.denote' ctx ≤ 0
      → d ∣ p₃.denote' ctx
      → OrOver n (cooper_dvd_left_split ctx p₁ p₂ p₃ d) := by
 unfold cooper_dvd_left_split
 cases p₁ <;> cases p₂ <;> cases p₃ <;> simp [cooper_dvd_left_cert, Poly.tail, -Poly.denote'_eq_denote]
 next a x p b y q c z s =>
 intro _ _; subst y z
 intro ha hb hd
 intro; subst n
 simp only [Poly.denote'_add, Poly.leadCoeff]
 intro h₁ h₂ h₃
 simp only [denote'_mul_combine_mul_addConst_eq]
 simp only [denote'_addConst_eq]
 exact cooper_dvd_left_core ha hb hd h₁ h₂ h₃

def cooper_dvd_left_split_ineq_cert (p₁ p₂ : Poly) (k : Int) (b : Int) (p' : Poly) : Bool :=
  let p  := p₁.tail
  let q  := p₂.tail
  let a  := p₁.leadCoeff
  let p₁ := p.mul b |>.combine (q.mul (-a))
  p₂.leadCoeff == b && p' == p₁.addConst (b*k)

theorem cooper_dvd_left_split_ineq (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (b : Int) (p' : Poly)
    : cooper_dvd_left_split ctx p₁ p₂ p₃ d k → cooper_dvd_left_split_ineq_cert p₁ p₂ k b p' → p'.denote' ctx ≤ 0 := by
  simp [cooper_dvd_left_split_ineq_cert, cooper_dvd_left_split]
  intros; subst p' b; simp [denote'_mul_combine_mul_addConst_eq]; assumption

def cooper_dvd_left_split_dvd1_cert (p₁ p' : Poly) (a : Int) (k : Int) : Bool :=
  a == p₁.leadCoeff && p' == p₁.tail.addConst k

theorem cooper_dvd_left_split_dvd1 (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (a : Int) (p' : Poly)
    : cooper_dvd_left_split ctx p₁ p₂ p₃ d k → cooper_dvd_left_split_dvd1_cert p₁ p' a k → a ∣ p'.denote' ctx := by
  simp [cooper_dvd_left_split_dvd1_cert, cooper_dvd_left_split]
  intros; subst a p'; simp; assumption

def cooper_dvd_left_split_dvd2_cert (p₁ p₃ : Poly) (d : Int) (k : Nat) (d' : Int) (p' : Poly): Bool :=
  let p  := p₁.tail
  let s  := p₃.tail
  let a  := p₁.leadCoeff
  let c  := p₃.leadCoeff
  let p₂ := p.mul c |>.combine (s.mul (-a))
  d' == a*d && p' == p₂.addConst (c*k)

theorem cooper_dvd_left_split_dvd2 (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (d' : Int) (p' : Poly)
    : cooper_dvd_left_split ctx p₁ p₂ p₃ d k → cooper_dvd_left_split_dvd2_cert p₁ p₃ d k d' p' → d' ∣ p'.denote' ctx := by
  simp [cooper_dvd_left_split_dvd2_cert, cooper_dvd_left_split]
  intros; subst d' p'; simp; assumption

private theorem cooper_left_core
    {a b p q x : Int} (a_neg : a < 0) (b_pos : 0 < b)
    (h₁ : a * x + p ≤ 0)
    (h₂ : b * x + q ≤ 0)
    : OrOver a.natAbs fun k =>
        b * p + (-a) * q + b * k ≤ 0 ∧
        a ∣ p + k := by
  have d_pos : (0 : Int) < 1 := by decide
  have h₃ : 1 ∣ 0*x + 0 := Int.one_dvd _
  have h := cooper_dvd_left_core a_neg b_pos d_pos h₁ h₂ h₃
  simp only [Int.mul_one, gcd_zero, ofNat_natAbs_of_nonpos (Int.le_of_lt a_neg), Int.ediv_neg,
    Int.ediv_self (Int.ne_of_lt a_neg), Int.reduceNeg, lcm_neg_right, lcm_one,
    Int.add_left_comm, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.dvd_zero,
    and_true] at h
  assumption

def cooper_left_cert (p₁ p₂ : Poly) (n : Nat) : Bool :=
  p₁.casesOn (fun _ => false) fun a x _ =>
  p₂.casesOn (fun _ => false) fun b y _ =>
   .and (x == y) <| .and (a < 0)  <| .and (b > 0)  <|
   n == a.natAbs

def cooper_left_split (ctx : Context) (p₁ p₂ : Poly) (k : Nat) : Prop :=
  let p  := p₁.tail
  let q  := p₂.tail
  let a  := p₁.leadCoeff
  let b  := p₂.leadCoeff
  let p₁ := p.mul b |>.combine (q.mul (-a))
  (p₁.addConst (b*k)).denote' ctx ≤ 0
  ∧ a ∣ (p.addConst k).denote' ctx

theorem cooper_left (ctx : Context) (p₁ p₂ : Poly) (n : Nat)
    : cooper_left_cert p₁ p₂ n
      → p₁.denote' ctx ≤ 0
      → p₂.denote' ctx ≤ 0
      → OrOver n (cooper_left_split ctx p₁ p₂) := by
 unfold cooper_left_split
 cases p₁ <;> cases p₂ <;> simp [cooper_left_cert, Poly.tail, -Poly.denote'_eq_denote]
 next a x p b y q =>
 intro; subst y
 intro ha hb
 intro; subst n
 simp only [Poly.denote'_add, Poly.leadCoeff]
 intro h₁ h₂
 have := cooper_left_core ha hb h₁ h₂
 simp only [denote'_mul_combine_mul_addConst_eq]
 simp only [denote'_addConst_eq]
 assumption

def cooper_left_split_ineq_cert (p₁ p₂ : Poly) (k : Int) (b : Int) (p' : Poly) : Bool :=
  let p  := p₁.tail
  let q  := p₂.tail
  let a  := p₁.leadCoeff
  let p₁ := p.mul b |>.combine (q.mul (-a))
  p₂.leadCoeff == b && p' == p₁.addConst (b*k)

theorem cooper_left_split_ineq (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (b : Int) (p' : Poly)
    : cooper_left_split ctx p₁ p₂ k → cooper_left_split_ineq_cert p₁ p₂ k b p' → p'.denote' ctx ≤ 0 := by
  simp [cooper_left_split_ineq_cert, cooper_left_split]
  intros; subst p' b; simp [denote'_mul_combine_mul_addConst_eq]; assumption

def cooper_left_split_dvd_cert (p₁ p' : Poly) (a : Int) (k : Int) : Bool :=
  a == p₁.leadCoeff && p' == p₁.tail.addConst k

theorem cooper_left_split_dvd (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (a : Int) (p' : Poly)
    : cooper_left_split ctx p₁ p₂ k → cooper_left_split_dvd_cert p₁ p' a k → a ∣ p'.denote' ctx := by
  simp [cooper_left_split_dvd_cert, cooper_left_split]
  intros; subst a p'; simp; assumption

private theorem cooper_dvd_right_core
    {a b c d s p q x : Int} (a_neg : a < 0) (b_pos : 0 < b) (d_pos : 0 < d)
    (h₁ : a * x + p ≤ 0)
    (h₂ : b * x + q ≤ 0)
    (h₃ : d ∣ c * x + s)
    : OrOver (Int.lcm b (b * d / Int.gcd (b * d) c)) fun k =>
      b * p + (-a) * q + (-a) * k ≤ 0 ∧
      b ∣ q + k ∧
      b * d ∣ (-c) * q + b * s + (-c) * k := by
  have a_pos' : 0 < -a := by apply Int.neg_pos_of_neg; assumption
  have h₁'    : p ≤ (-a)*x := by rw [Int.neg_mul, ← Lean.Omega.Int.add_le_zero_iff_le_neg']; assumption
  have h₂'    : b * x ≤ -q := by rw [← Lean.Omega.Int.add_le_zero_iff_le_neg', Int.add_comm]; assumption
  have ⟨k, h₁, h₂, h₃, h₄, h₅⟩ := Int.cooper_resolution_dvd_right a_pos' b_pos d_pos |>.mp ⟨x, h₁', h₂', h₃⟩
  simp only [Int.neg_mul, neg_gcd, lcm_neg_left, Int.mul_neg, Int.neg_neg, Int.neg_dvd] at *
  apply orOver_of_exists
  have hlt := ofNat_lt h₁ h₂
  replace h₃ := Int.add_le_add_right h₃ (-(a*q)); rw [Int.add_right_neg] at h₃
  have : -(a * k) + b * p + -(a * q) = b * p + -(a * q) + -(a * k) := by ac_rfl
  rw [this] at h₃; clear this
  rw [Int.sub_neg, Int.add_comm] at h₄
  have : -(c * k) + -(c * q) + b * s = -(c * q) + b * s + -(c * k) := by ac_rfl
  rw [this] at h₅; clear this
  exists k.toNat
  simp only [hlt, true_and, and_true, cast_toNat h₁, h₃, h₄, h₅]

def cooper_dvd_right_cert (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat) : Bool :=
  p₁.casesOn (fun _ => false) fun a x _ =>
  p₂.casesOn (fun _ => false) fun b y _ =>
  p₃.casesOn (fun _ => false) fun c z _ =>
   .and (x == y) <| .and (x == z) <|
   .and (a < 0)  <| .and (b > 0)  <|
   .and (d > 0)  <| n == Int.lcm b (b * d / Int.gcd (b * d) c)

def cooper_dvd_right_split (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) : Prop :=
  let p  := p₁.tail
  let q  := p₂.tail
  let s  := p₃.tail
  let a  := p₁.leadCoeff
  let b  := p₂.leadCoeff
  let c  := p₃.leadCoeff
  let p₁ := p.mul b |>.combine (q.mul (-a))
  let p₂ := q.mul (-c) |>.combine (s.mul b)
  (p₁.addConst ((-a)*k)).denote' ctx ≤ 0
  ∧ b ∣ (q.addConst k).denote' ctx
  ∧ b*d ∣ (p₂.addConst ((-c)*k)).denote' ctx

theorem cooper_dvd_right (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat)
    : cooper_dvd_right_cert p₁ p₂ p₃ d n
      → p₁.denote' ctx ≤ 0
      → p₂.denote' ctx ≤ 0
      → d ∣ p₃.denote' ctx
      → OrOver n (cooper_dvd_right_split ctx p₁ p₂ p₃ d) := by
 unfold cooper_dvd_right_split
 cases p₁ <;> cases p₂ <;> cases p₃ <;> simp [cooper_dvd_right_cert, Poly.tail, -Poly.denote'_eq_denote]
 next a x p b y q c z s =>
 intro _ _; subst y z
 intro ha hb hd
 intro; subst n
 simp only [Poly.denote'_add, Poly.leadCoeff]
 intro h₁ h₂ h₃
 have := cooper_dvd_right_core ha hb hd h₁ h₂ h₃
 simp only [denote'_mul_combine_mul_addConst_eq]
 simp only [denote'_addConst_eq, ←Int.neg_mul]
 exact cooper_dvd_right_core ha hb hd h₁ h₂ h₃

def cooper_dvd_right_split_ineq_cert (p₁ p₂ : Poly) (k : Int) (a : Int) (p' : Poly) : Bool :=
  let p  := p₁.tail
  let q  := p₂.tail
  let b  := p₂.leadCoeff
  let p₂ := p.mul b |>.combine (q.mul (-a))
  p₁.leadCoeff == a && p' == p₂.addConst ((-a)*k)

theorem cooper_dvd_right_split_ineq (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (a : Int) (p' : Poly)
    : cooper_dvd_right_split ctx p₁ p₂ p₃ d k → cooper_dvd_right_split_ineq_cert p₁ p₂ k a p' → p'.denote' ctx ≤ 0 := by
  simp [cooper_dvd_right_split_ineq_cert, cooper_dvd_right_split]
  intros; subst a p'; simp [denote'_mul_combine_mul_addConst_eq]; assumption

def cooper_dvd_right_split_dvd1_cert (p₂ p' : Poly) (b : Int) (k : Int) : Bool :=
  b == p₂.leadCoeff && p' == p₂.tail.addConst k

theorem cooper_dvd_right_split_dvd1 (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (b : Int) (p' : Poly)
    : cooper_dvd_right_split ctx p₁ p₂ p₃ d k → cooper_dvd_right_split_dvd1_cert p₂ p' b k → b ∣ p'.denote' ctx := by
  simp [cooper_dvd_right_split_dvd1_cert, cooper_dvd_right_split]
  intros; subst b p'; simp; assumption

def cooper_dvd_right_split_dvd2_cert (p₂ p₃ : Poly) (d : Int) (k : Nat) (d' : Int) (p' : Poly): Bool :=
  let q  := p₂.tail
  let s  := p₃.tail
  let b  := p₂.leadCoeff
  let c  := p₃.leadCoeff
  let p₂ := q.mul (-c) |>.combine (s.mul b)
  d' == b*d && p' == p₂.addConst ((-c)*k)

theorem cooper_dvd_right_split_dvd2 (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (d' : Int) (p' : Poly)
    : cooper_dvd_right_split ctx p₁ p₂ p₃ d k → cooper_dvd_right_split_dvd2_cert p₂ p₃ d k d' p' → d' ∣ p'.denote' ctx := by
  simp [cooper_dvd_right_split_dvd2_cert, cooper_dvd_right_split]
  intros; subst d' p'; simp; assumption

private theorem cooper_right_core
    {a b p q x : Int} (a_neg : a < 0) (b_pos : 0 < b)
    (h₁ : a * x + p ≤ 0)
    (h₂ : b * x + q ≤ 0)
    : OrOver b.natAbs fun k =>
      b * p + (-a) * q + (-a) * k ≤ 0 ∧
      b ∣ q + k := by
  have d_pos : (0 : Int) < 1 := by decide
  have h₃ : 1 ∣ 0*x + 0 := Int.one_dvd _
  have h := cooper_dvd_right_core a_neg b_pos d_pos h₁ h₂ h₃
  simp only [Int.mul_one, gcd_zero, Int.natAbs_of_nonneg (Int.le_of_lt b_pos), Int.ediv_neg,
    Int.ediv_self (Int.ne_of_gt b_pos), Int.reduceNeg, lcm_neg_right, lcm_one,
    Int.add_left_comm, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.dvd_zero,
    and_true, Int.neg_zero] at h
  assumption

def cooper_right_cert (p₁ p₂ : Poly) (n : Nat) : Bool :=
  p₁.casesOn (fun _ => false) fun a x _ =>
  p₂.casesOn (fun _ => false) fun b y _ =>
  .and (x == y) <| .and (a < 0)  <| .and (b > 0) <| n == b.natAbs

def cooper_right_split (ctx : Context) (p₁ p₂ : Poly) (k : Nat) : Prop :=
  let p  := p₁.tail
  let q  := p₂.tail
  let a  := p₁.leadCoeff
  let b  := p₂.leadCoeff
  let p₁ := p.mul b |>.combine (q.mul (-a))
  (p₁.addConst ((-a)*k)).denote' ctx ≤ 0
  ∧ b ∣ (q.addConst k).denote' ctx

theorem cooper_right (ctx : Context) (p₁ p₂ : Poly) (n : Nat)
    : cooper_right_cert p₁ p₂ n
      → p₁.denote' ctx ≤ 0
      → p₂.denote' ctx ≤ 0
      → OrOver n (cooper_right_split ctx p₁ p₂) := by
 unfold cooper_right_split
 cases p₁ <;> cases p₂ <;> simp [cooper_right_cert, Poly.tail, -Poly.denote'_eq_denote]
 next a x p b y q =>
 intro; subst y
 intro ha hb
 intro; subst n
 simp only [Poly.denote'_add, Poly.leadCoeff]
 intro h₁ h₂
 have := cooper_right_core ha hb h₁ h₂
 simp only [denote'_mul_combine_mul_addConst_eq]
 simp only [denote'_addConst_eq, ←Int.neg_mul]
 assumption

def cooper_right_split_ineq_cert (p₁ p₂ : Poly) (k : Int) (a : Int) (p' : Poly) : Bool :=
  let p  := p₁.tail
  let q  := p₂.tail
  let b  := p₂.leadCoeff
  let p₂ := p.mul b |>.combine (q.mul (-a))
  p₁.leadCoeff == a && p' == p₂.addConst ((-a)*k)

theorem cooper_right_split_ineq (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (a : Int) (p' : Poly)
    : cooper_right_split ctx p₁ p₂ k → cooper_right_split_ineq_cert p₁ p₂ k a p' → p'.denote' ctx ≤ 0 := by
  simp [cooper_right_split_ineq_cert, cooper_right_split]
  intros; subst a p'; simp [denote'_mul_combine_mul_addConst_eq]; assumption

def cooper_right_split_dvd_cert (p₂ p' : Poly) (b : Int) (k : Int) : Bool :=
  b == p₂.leadCoeff && p' == p₂.tail.addConst k

theorem cooper_right_split_dvd (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (b : Int) (p' : Poly)
    : cooper_right_split ctx p₁ p₂ k → cooper_right_split_dvd_cert p₂ p' b k → b ∣ p'.denote' ctx := by
  simp [cooper_right_split_dvd_cert, cooper_right_split]
  intros; subst b p'; simp; assumption

private theorem one_emod_eq_one {a : Int} (h : a > 1) : 1 % a = 1 := by
  have aux₁ := Int.ediv_add_emod 1 a
  have : 1 / a = 0 := Int.ediv_eq_zero_of_lt (by decide) h
  simp [this] at aux₁
  assumption

private theorem ex_of_dvd {α β a b d x : Int}
    (h₀ : d > 1)
    (h₁ : d ∣ a*x + b)
    (h₂ : α * a + β * d = 1)
    : ∃ k, x = k * d + (- α * b) % d := by
  have ⟨k, h₁⟩ := h₁
  have aux₁ : (α * a) % d = 1 := by
    replace h₂ := congrArg (· % d) h₂; simp at h₂
    rw [one_emod_eq_one h₀] at h₂
    assumption
  have : ((α * a) * x) % d = (- α * b) % d := by
    replace h₁ := congrArg (α * ·) h₁; simp only at h₁
    rw [Int.mul_add] at h₁
    replace h₁ := congrArg (· - α * b) h₁; simp only [Int.add_sub_cancel] at h₁
    rw [← Int.mul_assoc, Int.mul_left_comm, Int.sub_eq_add_neg] at h₁
    replace h₁ := congrArg (· % d) h₁; simp only at h₁
    rw [Int.add_emod, Int.mul_emod_right, Int.zero_add, Int.emod_emod, ← Int.neg_mul] at h₁
    assumption
  have : x % d = (- α * b) % d := by
    rw [Int.mul_emod, aux₁, Int.one_mul, Int.emod_emod] at this
    assumption
  have : x = (x / d)*d + (- α * b) % d := by
    conv => lhs; rw [← Int.ediv_add_emod x d]
    rw [Int.mul_comm, this]
  exists x / d

private theorem cdiv_le {a d k : Int} : d > 0 → a ≤ k * d → cdiv a d ≤ k := by
  intro h₁ h₂
  simp [cdiv]
  replace h₂ := Int.neg_le_neg h₂
  rw [← Int.neg_mul] at h₂
  replace h₂ := Int.le_ediv_of_mul_le h₁ h₂
  replace h₂ := Int.neg_le_neg h₂
  simp at h₂
  assumption

private theorem cooper_unsat'_helper {a b d c k x : Int}
    (d_pos : d > 0)
    (h₁ : x = k * d + c)
    (h₂ : a ≤ x)
    (h₃ : x ≤ b)
    : ¬ b < (cdiv (a - c) d) * d + c := by
  intro h₄
  have aux₁ : cdiv (a - c) d ≤ k := by
    rw [h₁] at h₂
    replace h₂ := Int.sub_right_le_of_le_add h₂
    exact cdiv_le d_pos h₂
  have aux₂ : cdiv (a - c) d * d ≤ k * d := Int.mul_le_mul_of_nonneg_right aux₁ (Int.le_of_lt d_pos)
  have aux₃ : cdiv (a - c) d * d + c ≤ k * d + c := Int.add_le_add_right aux₂ _
  have aux₄ : cdiv (a - c) d * d + c ≤ x := by rw [←h₁] at aux₃; assumption
  have aux₅ : cdiv (a - c) d * d + c ≤ b := Int.le_trans aux₄ h₃
  have := Int.lt_of_le_of_lt aux₅ h₄
  exact Int.lt_irrefl _ this

private theorem cooper_unsat' {a c b d e α β x : Int}
    (h₁ : d > 1)
    (h₂ : d ∣ c*x + e)
    (h₃ : α * c + β * d = 1)
    (h₄ : (-1)*x + a ≤ 0)
    (h₅ : x + b ≤ 0)
    (h₆ : -b < cdiv (a - -α * e % d) d * d + -α * e % d)
    : False := by
  have ⟨k, h⟩ := ex_of_dvd h₁ h₂ h₃
  have d_pos : d > 0 := Int.lt_trans (by decide) h₁
  replace h₄ := Int.le_neg_add_of_add_le h₄; simp at h₄
  replace h₅ := Int.neg_le_neg (Int.le_neg_add_of_add_le h₅); simp at h₅
  have := cooper_unsat'_helper d_pos h h₄ h₅
  exact this h₆

abbrev Poly.casesOnAdd (p : Poly) (k : Int → Var → Poly → Bool) : Bool :=
  p.casesOn (fun _  => false) k

abbrev Poly.casesOnNum (p : Poly) (k : Int → Bool) : Bool :=
  p.casesOn k (fun _ _ _ => false)

def cooper_unsat_cert (p₁ p₂ p₃ : Poly) (d : Int) (α β : Int) : Bool :=
  p₁.casesOnAdd fun k₁ x p₁ =>
  p₂.casesOnAdd fun k₂ y p₂ =>
  p₃.casesOnAdd fun c z p₃ =>
  p₁.casesOnNum fun a =>
  p₂.casesOnNum fun b =>
  p₃.casesOnNum fun e =>
  (k₁ == -1) |>.and (k₂ == 1) |>.and
  (x == y) |>.and (x == z) |>.and
  (d > 1) |>.and (α * c + β * d == 1) |>.and
  (-b < cdiv (a - -α * e % d) d * d + -α * e % d)

theorem cooper_unsat (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (α β : Int)
   : cooper_unsat_cert p₁ p₂ p₃ d α β →
     p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx → False := by
  unfold cooper_unsat_cert <;> cases p₁ <;> cases p₂ <;> cases p₃ <;> simp only [Poly.casesOnAdd,
    Bool.false_eq_true, Poly.denote'_add, mul_def, add_def, false_implies]
  next k₁ x p₁ k₂ y p₂ c z p₃ =>
  cases p₁ <;> cases p₂ <;> cases p₃ <;> simp only [Poly.casesOnNum, Int.reduceNeg,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_imp, Bool.false_eq_true,
    mul_def, add_def, false_implies, Poly.denote]
  next a b e =>
  intro _ _ _ _; subst k₁ k₂ y z
  intro h₁ h₃ h₆; generalize Var.denote ctx x = x'
  intro h₄ h₅ h₂
  rw [Int.one_mul] at h₅
  exact cooper_unsat' h₁ h₂ h₃ h₄ h₅ h₆

theorem ediv_emod (x y : Int) : -1 * x + y * (x / y) + x % y = 0 := by
  rw [Int.add_assoc, Int.ediv_add_emod x y, Int.add_comm]
  simp
  rw [← Int.sub_eq_add_neg, Int.sub_self]

theorem emod_nonneg (x y : Int) : y != 0 → -1 * (x % y) ≤ 0 := by
  simp; intro h
  have := Int.neg_le_neg (Int.emod_nonneg x h)
  simp at this
  assumption

def emod_le_cert (y n : Int) : Bool :=
  y != 0 && n == 1 - y.natAbs

theorem emod_le (x y : Int) (n : Int) : emod_le_cert y n → x % y + n ≤ 0 := by
  simp [emod_le_cert]
  intro h₁
  cases Int.lt_or_gt_of_ne h₁
  next h =>
    rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)]
    simp only [Int.sub_neg]
    intro; subst n
    rw [Int.add_assoc, Int.add_left_comm]
    apply Int.add_le_of_le_sub_left
    rw [Int.zero_sub, Int.add_comm]
    have : 0 < -y := by
      have := Int.neg_lt_neg h
      rw [Int.neg_zero] at this
      assumption
    have := Int.emod_lt_of_pos x this
    rw [Int.emod_neg] at this
    exact this
  next h =>
    rw [Int.natAbs_of_nonneg (Int.le_of_lt h)]
    intro; subst n
    rw [Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_comm]
    apply Int.add_le_of_le_sub_left
    simp only [Int.add_comm, Int.sub_neg, Int.add_zero]
    exact Int.emod_lt_of_pos x h

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
