/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Int.LemmasAux
public import Init.Data.Int.Cooper
import all Init.Data.Int.Gcd
public import Init.Data.AC
import all Init.Data.AC
import Init.LawfulBEqTactics
public section
namespace Int.Linear

/-! Helper definitions and theorems for constructing linear arithmetic proofs. -/

abbrev Var := Nat
abbrev Context := Lean.RArray Int

abbrev Var.denote (ctx : Context) (v : Var) : Int :=
  ctx.get v

inductive Expr where
  | num  (v : Int)
  | var  (i : Var)
  | add  (a b : Expr)
  | sub  (a b : Expr)
  | neg (a : Expr)
  | mulL (k : Int) (a : Expr)
  | mulR (a : Expr) (k : Int)
  deriving Inhabited, @[expose] BEq

abbrev Expr.denote (ctx : Context) : Expr → Int
  | .add a b  => denote ctx a + denote ctx b
  | .sub a b  => denote ctx a - denote ctx b
  | .neg a    => - denote ctx a
  | .num k    => k
  | .var v    => v.denote ctx
  | .mulL k e => k * denote ctx e
  | .mulR e k => denote ctx e * k

set_option allowUnsafeReducibility true
attribute [semireducible] Var.denote Expr.denote

inductive Poly where
  | num (k : Int)
  | add (k : Int) (v : Var) (p : Poly)
  deriving @[expose] BEq, ReflBEq, LawfulBEq

@[expose]
protected noncomputable def Poly.beq' (p₁ : Poly) : Poly → Bool :=
  Poly.rec
    (fun k₁ p₂ => Poly.rec (fun k₂ => Int.beq' k₁ k₂) (fun _ _ _ _ => false) p₂)
    (fun k₁ v₁ _ ih p₂ =>
      Poly.rec
        (fun _ => false)
        (fun k₂ v₂ p₂ _ => (Int.beq' k₁ k₂).and' ((Nat.beq v₁ v₂).and' (ih p₂))) p₂)
    p₁

@[simp] theorem Poly.beq'_eq (p₁ p₂ : Poly) : p₁.beq' p₂ = (p₁ = p₂) := by
  induction p₁ generalizing p₂ <;> cases p₂ <;> simp [Poly.beq']
  rename_i k₁ v₁ p₁ ih v₂ m₂ p₂
  rw [← eq_iff_iff]
  intro _ _; subst k₁ v₁
  simp [← ih p₂, ← Bool.and'_eq_and]; rfl

abbrev Poly.denote (ctx : Context) (p : Poly) : Int :=
  match p with
  | .num k => k
  | .add k v p => k * v.denote ctx + denote ctx p

noncomputable abbrev Poly.denote'.go (ctx : Context) (p : Poly) : Int → Int :=
  Poly.rec
    (fun k r => Bool.rec
      (r + k)
      r
      (Int.beq' k 0))
    (fun k v _ ih r => Bool.rec
      (ih (r + k * v.denote ctx))
      (ih (r + v.denote ctx))
      (Int.beq' k 1))
    p

/--
Similar to `Poly.denote`, but produces a denotation better for `simp +arith`.
Remark: we used to convert `Poly` back into `Expr` to achieve that.
-/
noncomputable abbrev Poly.denote' (ctx : Context) (p : Poly) : Int :=
  Poly.rec (fun k => k)
    (fun k v p _ => Bool.rec
      (denote'.go ctx p (k * v.denote ctx))
      (denote'.go ctx p (v.denote ctx))
      (Int.beq' k 1))
    p

attribute [semireducible] Poly.denote Poly.denote' Poly.denote'.go

@[simp] theorem Poly.denote'_go_eq_denote (ctx : Context) (p : Poly) (r : Int) : denote'.go ctx p r = p.denote ctx + r := by
  induction p generalizing r
  next k =>
    simp [denote'.go, denote]
    cases h : k.beq' 0 <;> simp [*]
    · rw [Int.add_comm]
    · simp [Int.beq'_eq_beq] at h; simp [h]
  next k v p ih =>
    simp [denote, denote'.go]
    cases h : k.beq' 1 <;> simp [*]
    next =>
      show denote'.go ctx p (r + k * v.denote ctx) = _
      rw [ih]; ac_rfl
    next =>
      show denote'.go ctx p (r + v.denote ctx) = _
      simp [Int.beq'_eq_beq] at h
      simp [ih, h]; ac_rfl

theorem Poly.denote'_eq_denote (ctx : Context) (p : Poly) : p.denote' ctx = p.denote ctx := by
  unfold Poly.denote' Poly.denote; cases p <;> simp
  next k v p =>
    cases h : k.beq' 1 <;> simp [*]
    next => ac_rfl
    next =>
      simp [Int.beq'_eq_beq] at h
      simp [h]; ac_rfl

theorem Poly.denote'_add (ctx : Context) (a : Int) (x : Var) (p : Poly) : (Poly.add a x p).denote' ctx = a * x.denote ctx + p.denote ctx := by
  simp [Poly.denote'_eq_denote, denote]

@[expose]
def Poly.addConst (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k+k')
  | .add k' v' p => .add k' v' (addConst p k)

@[expose] noncomputable def Poly.addConst_k (p : Poly) (k : Int) : Poly :=
   Poly.rec (fun k' => .num (Int.add k k')) (fun k' v' _ ih => .add k' v' ih) p

@[simp] theorem Poly.addConst_k_eq_addConst (p : Poly) (k : Int) : p.addConst_k k = p.addConst k := by
  fun_induction Poly.addConst
  next => simp [addConst_k]
  next k' v' p ih => simp [addConst_k, ← ih]

@[expose]
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
@[expose]
def Poly.norm (p : Poly) : Poly :=
  match p with
  | .num k => .num k
  | .add k v p => (norm p).insert k v

@[expose]
def Poly.append (p₁ p₂ : Poly) : Poly :=
  match p₁ with
  | .num k₁ => p₂.addConst k₁
  | .add k x p₁ => .add k x (append p₁ p₂)

@[expose]
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

@[expose] abbrev hugeFuel := 100000000

@[expose]
def Poly.combine (p₁ p₂ : Poly) : Poly :=
  combine' hugeFuel p₁ p₂

/-- Converts the given expression into a polynomial. -/
@[expose]
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
@[expose]
def Expr.norm (e : Expr) : Poly :=
  e.toPoly'.norm

/--
Returns the ceiling of the division `a / b`. That is, the result is equivalent to `⌈a / b⌉`.
Examples:
- `cdiv 7 3` returns `3`
- `cdiv (-7) 3` returns `-2`.
-/
@[expose]
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
@[expose]
def cmod (a b : Int) : Int :=
  -((-a)%b)

theorem cdiv_add_cmod (a b : Int) : b*(cdiv a b) + cmod a b = a := by
  unfold cdiv cmod
  have := Int.mul_ediv_add_emod (-a) b
  have := congrArg (Neg.neg) this
  simp at this
  conv => rhs; rw[← this]
  rw [Int.neg_add, ←Int.neg_mul, Int.neg_mul_comm]

theorem cmod_gt_of_pos (a : Int) {b : Int} (h : 0 < b) : cmod a b > -b :=
  Int.neg_lt_neg (Int.emod_lt_of_pos (-a) h)

theorem cmod_nonpos (a : Int) {b : Int} (h : b ≠ 0) : cmod a b ≤ 0 := by
  have := Int.neg_le_neg (Int.emod_nonneg (-a) h)
  simpa [cmod] using this

theorem cmod_eq_zero_iff_emod_eq_zero (a b : Int) : cmod a b = 0 ↔ a%b = 0 := by
  unfold cmod
  have := @Int.emod_eq_emod_iff_emod_sub_eq_zero b b a
  simp only [emod_self, sub_emod_left] at this
  rw [Int.neg_eq_zero, ← this, Eq.comm]

private abbrev div_mul_cancel_of_mod_zero :=
  @Int.ediv_mul_cancel_of_emod_eq_zero

theorem cdiv_eq_div_of_divides {a b : Int} (h : a % b = 0) : a/b = cdiv a b := by
  replace h := div_mul_cancel_of_mod_zero h
  have hz : a % b = 0 := by
    have := Int.mul_ediv_add_emod a b
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
@[expose]
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
@[expose]
def Poly.div (k : Int) : Poly → Poly
  | .num k' => .num (cdiv k' k)
  | .add k' x p => .add (k'/k) x (div k p)

/--
Returns `true` if `k` divides all coefficients and the constant of the given
linear polynomial.
-/
@[expose]
def Poly.divAll (k : Int) : Poly → Bool
  | .num k' => k' % k == 0
  | .add k' _ p => k' % k == 0 && divAll k p

/--
Returns `true` if `k` divides all coefficients of the given linear polynomial.
-/
@[expose]
def Poly.divCoeffs (k : Int) : Poly → Bool
  | .num _ => true
  | .add k' _ p => k' % k == 0 && divCoeffs k p

/--
`p.mul k` multiplies all coefficients and constant of the polynomial `p` by `k`.
-/
@[expose]
def Poly.mul' (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k*k')
  | .add k' v p => .add (k*k') v (mul' p k)

@[expose]
def Poly.mul (p : Poly) (k : Int) : Poly :=
  if k == 0 then
    .num 0
  else
    p.mul' k

@[expose] noncomputable def Poly.mul_k (p : Poly) (k : Int) : Poly :=
  Bool.rec
    (Poly.rec (fun k' => .num (Int.mul k k'))
      (fun k' v _ ih => .add (Int.mul k k') v ih)
      p)
    (.num 0)
    (Int.beq' k 0)

@[simp] theorem Poly.mul_k_eq_mul (k : Int) (p : Poly) : p.mul_k k = p.mul k := by
  simp [mul_k, mul]; split
  next =>
    have h : Int.beq' k 0 = true := by simp [*]
    simp [h]
  next =>
    have h₁ : Int.beq' k 0 = false := by rw [← Bool.not_eq_true, Int.beq'_eq]; assumption
    simp [h₁]
    induction p
    next => rfl
    next k m p ih => simp [mul', ← ih]

@[expose] noncomputable def Poly.combine_mul_k' (fuel : Nat) (a b : Int) : Poly → Poly → Poly :=
  Nat.rec (fun p₁ p₂ => Poly.append (p₁.mul a) (p₂.mul b))
    (fun _ ih p₁ => Poly.rec
      (fun k₁ p₂ => Poly.rec
        (fun k₂ => .num (Int.add (Int.mul a k₁) (Int.mul b k₂)))
        (fun a₂ x₂ p₂ _ => .add (Int.mul b a₂) x₂ (ih p₁ p₂))
        p₂)
      (fun a₁ x₁ p₁ _ p₂ => Poly.rec
        (fun _ => .add (Int.mul a a₁) x₁ (ih p₁ p₂))
        (fun a₂ x₂ p₂ _ => Bool.rec
          (Bool.rec
            (.add (Int.mul b a₂) x₂ (ih (.add a₁ x₁ p₁) p₂))
            (.add (Int.mul a a₁) x₁ (ih p₁ (.add a₂ x₂ p₂)))
            (Nat.blt x₂ x₁))
          (let a := Int.add (Int.mul a a₁) (Int.mul b a₂)
           Bool.rec (.add a x₁ (ih p₁ p₂)) (ih p₁ p₂) (Int.beq' a 0))
          (Nat.beq x₁ x₂))
        p₂)
      p₁)
    fuel

@[expose] noncomputable def Poly.combine_mul_k (a b : Int) (p₁ p₂ : Poly) : Poly :=
  Bool.rec
    (Bool.rec (combine_mul_k' hugeFuel a b p₁ p₂) (p₁.mul_k a) (Int.beq' b 0))
    (p₂.mul_k b)
    (Int.beq' a 0)

@[simp] theorem Poly.denote_mul (ctx : Context) (p : Poly) (k : Int) : (p.mul k).denote ctx = k * p.denote ctx := by
  simp [mul]
  split
  next => simp [*, denote]
  next =>
    induction p <;> simp [mul', denote, *]
    rw [Int.mul_assoc, Int.mul_add]

attribute [local simp] Int.add_comm Int.add_assoc Int.add_left_comm Int.add_mul Int.mul_add
attribute [local simp] Poly.insert Poly.denote Poly.norm Poly.addConst

theorem Poly.denote_addConst (ctx : Context) (p : Poly) (k : Int) : (p.addConst k).denote ctx = p.denote ctx + k := by
  induction p <;> simp [*]

attribute [local simp] Poly.denote_addConst

theorem Poly.denote_insert (ctx : Context) (k : Int) (v : Var) (p : Poly) :
    (p.insert k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  fun_induction p.insert k v <;>
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
    sorry

theorem Poly.denote_combine (ctx : Context) (p₁ p₂ : Poly) : (p₁.combine p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  simp [combine, denote_combine']

theorem Poly.denote_combine_mul_k (ctx : Context) (a b : Int) (p₁ p₂ : Poly) : (p₁.combine_mul_k a b p₂).denote ctx = a * p₁.denote ctx + b * p₂.denote ctx := by
  unfold combine_mul_k
  cases h₁ : Int.beq' a 0 <;> simp at h₁ <;> simp [*]
  cases h₂ : Int.beq' b 0 <;> simp at h₂ <;> simp [*]
  generalize hugeFuel = fuel
  induction fuel generalizing p₁ p₂
  next => show ((p₁.mul a).append (p₂.mul b)).denote ctx = _; simp
  next fuel ih =>
  cases p₁ <;> cases p₂ <;> simp [combine_mul_k']
  next k₁ k₂ v₂ p₂ =>
    show _ + (combine_mul_k' fuel a b (.num k₁) p₂).denote ctx = _
    simp [ih, Int.mul_assoc]
  next k₁ v₁ p₁ k₂ =>
    show _ + (combine_mul_k' fuel a b p₁ (.num k₂)).denote ctx = _
    simp [ih, Int.mul_assoc]
  next k₁ v₁ p₁ k₂ v₂ p₂ =>
    cases h₁ : Nat.beq v₁ v₂ <;> simp
    next =>
      cases h₂ : Nat.blt v₂ v₁ <;> simp
      next =>
        show _ + (combine_mul_k' fuel a b (add k₁ v₁ p₁) p₂).denote ctx = _
        simp [ih, Int.mul_assoc]
      next =>
        show _ + (combine_mul_k' fuel a b p₁ (add k₂ v₂ p₂)).denote ctx = _
        simp [ih, Int.mul_assoc]
    next =>
      simp at h₁; subst v₂
      cases h₂ : (a * k₁ + b * k₂).beq' 0 <;> simp
      next =>
        show a * k₁ * v₁.denote ctx + (b * k₂ * v₁.denote ctx + (combine_mul_k' fuel a b p₁ p₂).denote ctx) = _
        simp [ih, Int.mul_assoc]
      next =>
        simp at h₂
        show (combine_mul_k' fuel a b p₁ p₂).denote ctx = _
        simp [ih, ← Int.mul_assoc, ← Int.add_mul, h₂]

attribute [local simp] Poly.denote_combine Poly.denote_combine_mul_k

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
    simp
  | case3 k i => simp [toPoly'.go]
  | case4 k a b iha ihb => simp [toPoly'.go, iha, ihb]
  | case5 k a b iha ihb =>
    simp [toPoly'.go, iha, ihb, Int.mul_sub]
    rw [Int.sub_eq_add_neg, ←Int.neg_mul, Int.add_assoc]
  | case6 k k' a h
  | case8 k a k' h =>
    simp only [toPoly'.go, h]
    simp [eq_of_beq h]
  | case7 k a k' h ih =>
    simp only [toPoly'.go, h, cond_false]
    simpa [denote, ← Int.mul_assoc] using ih
  | case9 k a h h ih =>
    simp only [toPoly'.go, h, cond_false]
    simp only [mul_def, denote]
    rw [Int.mul_comm (denote _ _) _]
    simpa [Int.mul_assoc] using ih
  | case10 k a ih => simp [toPoly'.go, ih, Int.neg_mul, Int.mul_neg]

theorem Expr.denote_norm (ctx : Context) (e : Expr) : e.norm.denote ctx = e.denote ctx := by
  simp [norm, toPoly', Expr.denote_toPoly'_go]

attribute [local simp] Expr.denote_norm
attribute [local simp] Poly.denote'_eq_denote

theorem Expr.eq_of_norm_eq (ctx : Context) (e : Expr) (p : Poly) (h : e.norm.beq' p) : e.denote ctx = p.denote' ctx := by
  simp at h
  have h := congrArg (Poly.denote ctx) h
  simp at h
  simp [*]

@[expose]
noncomputable def norm_eq_cert (lhs rhs : Expr) (p : Poly) : Bool :=
  p.beq' (lhs.sub rhs).norm

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

@[expose]
noncomputable def norm_eq_var_cert (lhs rhs : Expr) (x y : Var) : Bool :=
  (lhs.sub rhs).norm.beq' (.add 1 x (.add (-1) y (.num 0)))

theorem norm_eq_var (ctx : Context) (lhs rhs : Expr) (x y : Var) (h : norm_eq_var_cert lhs rhs x y)
    : (lhs.denote ctx = rhs.denote ctx) = (x.denote ctx = y.denote ctx) := by
  simp [norm_eq_var_cert] at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  rw [←Int.sub_eq_zero, h, ← @Int.sub_eq_zero (Var.denote ctx x), Int.sub_eq_add_neg]

@[expose]
noncomputable def norm_eq_var_const_cert (lhs rhs : Expr) (x : Var) (k : Int) : Bool :=
  (lhs.sub rhs).norm.beq' (.add 1 x (.num (-k)))

theorem norm_eq_var_const (ctx : Context) (lhs rhs : Expr) (x : Var) (k : Int) (h : norm_eq_var_const_cert lhs rhs x k)
    : (lhs.denote ctx = rhs.denote ctx) = (x.denote ctx = k) := by
  simp [norm_eq_var_const_cert] at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  rw [←Int.sub_eq_zero, h, Int.add_comm, Int.add_neg_eq_sub, Int.sub_eq_zero]

private theorem mul_eq_zero_iff (a k : Int) (h₁ : k > 0) : k * a = 0 ↔ a = 0 := by
  conv => lhs; rw [← Int.mul_zero k]
  apply Int.mul_eq_mul_left_iff
  exact Int.ne_of_gt h₁

theorem norm_eq_coeff' (ctx : Context) (p p' : Poly) (k : Int) : p = p'.mul k → k > 0 → (p.denote ctx = 0 ↔ p'.denote ctx = 0) := by
  intro; subst p; intro h; simp [mul_eq_zero_iff, *]

@[expose]
noncomputable def norm_eq_coeff_cert (lhs rhs : Expr) (p : Poly) (k : Int) : Bool :=
  (lhs.sub rhs).norm.beq' (p.mul_k k) |>.and' (Int.blt' 0 k)

theorem norm_eq_coeff (ctx : Context) (lhs rhs : Expr) (p : Poly) (k : Int)
    : norm_eq_coeff_cert lhs rhs p k → (lhs.denote ctx = rhs.denote ctx) = (p.denote' ctx = 0) := by
  simp [norm_eq_coeff_cert]
  rw [norm_eq ctx lhs rhs (lhs.sub rhs).norm, Poly.denote'_eq_denote]
  · apply norm_eq_coeff'
  · unfold norm_eq_cert; simp

private theorem mul_le_zero_iff (a k : Int) (h₁ : k > 0) : k * a ≤ 0 ↔ a ≤ 0 := by
  constructor
  · intro h
    rw [← Int.mul_zero k] at h
    exact Int.le_of_mul_le_mul_left h h₁
  · intro h
    replace h := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt h₁)
    simp at h; assumption

private theorem norm_le_coeff' (ctx : Context) (p p' : Poly) (k : Int) : p = p'.mul k → k > 0 → (p.denote ctx ≤ 0 ↔ p'.denote ctx ≤ 0) := by
  simp
  intro; subst p; intro h; simp [mul_le_zero_iff, *]

theorem norm_le_coeff (ctx : Context) (lhs rhs : Expr) (p : Poly) (k : Int)
    : norm_eq_coeff_cert lhs rhs p k → (lhs.denote ctx ≤ rhs.denote ctx) = (p.denote' ctx ≤ 0) := by
  simp [norm_eq_coeff_cert]
  rw [norm_le ctx lhs rhs (lhs.sub rhs).norm, Poly.denote'_eq_denote]
  · apply norm_le_coeff'
  · unfold norm_eq_cert; simp

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

@[expose]
noncomputable def norm_le_coeff_tight_cert (lhs rhs : Expr) (p : Poly) (k : Int) : Bool :=
  let p' := lhs.sub rhs |>.norm
  (Int.blt' 0 k) |>.and' (p'.divCoeffs k |>.and' (p.beq' (p'.div k)))

theorem norm_le_coeff_tight (ctx : Context) (lhs rhs : Expr) (p : Poly) (k : Int)
    : norm_le_coeff_tight_cert lhs rhs p k → (lhs.denote ctx ≤ rhs.denote ctx) = (p.denote' ctx ≤ 0) := by
  simp [norm_le_coeff_tight_cert]
  rw [norm_le ctx lhs rhs (lhs.sub rhs).norm, Poly.denote'_eq_denote]
  · apply eq_of_norm_eq_of_divCoeffs
  · unfold norm_eq_cert; simp

@[expose]
def Poly.isUnsatEq (p : Poly) : Bool :=
  match p with
  | .num k => k != 0
  | _ => false

@[expose]
def Poly.isValidEq (p : Poly) : Bool :=
  match p with
  | .num k => k == 0
  | _ => false

@[expose] noncomputable def Poly.isUnsatEq_k (p : Poly) : Bool :=
  Poly.rec (fun k => Bool.not' (Int.beq' k 0)) (fun _ _ _ _ => false) p

theorem eq_eq_false (ctx : Context) (lhs rhs : Expr) : (lhs.sub rhs).norm.isUnsatEq_k → (lhs.denote ctx = rhs.denote ctx) = False := by
  simp [Poly.isUnsatEq_k]; generalize h : (lhs.sub rhs).norm = p
  cases p <;> simp
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

@[expose]
def Poly.isUnsatLe (p : Poly) : Bool :=
  match p with
  | .num k => k > 0
  | _ => false

@[expose]
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

@[expose]
noncomputable def unsatEqDivCoeffCert (lhs rhs : Expr) (k : Int) : Bool :=
  let p := (lhs.sub rhs).norm
  p.divCoeffs k |>.and' (Int.blt' 0 k |>.and' (cmod p.getConst k < 0))

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

@[expose]
def Poly.gcdCoeffs : Poly → Int → Int
  | .num _, k => k
  | .add k' _ p, k => gcdCoeffs p (gcd k' k)

theorem Poly.gcd_dvd_const {ctx : Context} {p : Poly} {k : Int} (h : k ∣ p.denote ctx) : p.gcdCoeffs k ∣ p.getConst := by
  induction p generalizing k <;> simp_all [gcdCoeffs]
  next k' x p ih =>
    rw [Int.add_comm] at h
    exact ih (gcd_dvd_step h)

@[expose]
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

theorem norm_dvd (ctx : Context) (k : Int) (e : Expr) (p : Poly) : e.norm.beq' p → (k ∣ e.denote ctx) = (k ∣ p.denote' ctx) := by
  simp; intro h; simp [← h]

theorem dvd_eq_false (ctx : Context) (k : Int) (e : Expr) (h : e.norm.isUnsatDvd k) : (k ∣ e.denote ctx) = False := by
  rw [norm_dvd ctx k e e.norm]
  · apply dvd_eq_false' ctx k e.norm h
  · simp

@[expose]
noncomputable def dvd_coeff_cert (k₁ : Int) (p₁ : Poly) (k₂ : Int) (p₂ : Poly) (k : Int) : Bool :=
  k != 0 |>.and' (k₁.beq' (Int.mul k k₂) |>.and' (p₁.beq' (p₂.mul_k k)))

@[expose]
noncomputable def norm_dvd_gcd_cert (k₁ : Int) (e₁ : Expr) (k₂ : Int) (p₂ : Poly) (k : Int) : Bool :=
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

@[expose]
noncomputable def dvd_elim_cert (k₁ : Int) (p₁ : Poly) (k₂ : Int) (p₂ : Poly) : Bool :=
  Poly.rec
    (fun _ => false)
    (fun a _ p _ => k₂.beq' (gcd k₁ a) |>.and' (p₂.beq' p))
    p₁

theorem dvd_elim (ctx : Context) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (p₂ : Poly)
    : dvd_elim_cert k₁ p₁ k₂ p₂ → k₁ ∣ p₁.denote' ctx → k₂ ∣ p₂.denote' ctx := by
  rcases p₁ <;> simp [dvd_elim_cert]
  rename_i a _ p
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

@[expose]
noncomputable def dvd_solve_combine_cert (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly) (g α β : Int) : Bool :=
  Poly.rec (fun _ => false)
    (fun a₁ x₁ p₁ _ => Poly.rec (fun _ => false)
      (fun a₂ x₂ p₂ _ =>
        x₁.beq x₂ |>.and'
        (g.beq' (α*a₁*d₂ + β*a₂*d₁) |>.and'
        (d.beq' (d₁*d₂) |>.and'
        (p.beq' (.add g x₁ (p₁.combine_mul_k (α*d₂) (β*d₁) p₂))))))
      p₂)
    p₁

theorem dvd_solve_combine (ctx : Context) (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly) (g α β : Int)
    : dvd_solve_combine_cert d₁ p₁ d₂ p₂ d p g α β → d₁ ∣ p₁.denote' ctx → d₂ ∣ p₂.denote' ctx → d ∣ p.denote' ctx := by
  simp [dvd_solve_combine_cert]
  cases p₁ <;> cases p₂ <;> simp
  rename_i a₁ x₁ p₁ a₂ x₂ p₂
  intro _ hg hd hp; subst x₁ p
  simp
  intro h₁ h₂
  rw [Int.add_comm] at h₁ h₂
  rw [Int.add_comm _ (g * x₂.denote ctx), Int.add_left_comm, ← Int.add_assoc, hd]
  exact dvd_solve_combine' hg.symm h₁ h₂

@[expose]
noncomputable def dvd_solve_elim_cert (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly) : Bool :=
  match p₁, p₂ with
  | .add a₁ x₁ p₁, .add a₂ x₂ p₂ =>
    x₁.beq x₂ &&
    (d.beq' (Int.gcd (a₁*d₂) (a₂*d₁)) &&
     p.beq' (p₁.combine_mul_k a₂ (- a₁) p₂))
  | _, _ => false

theorem dvd_solve_elim (ctx : Context) (d₁ : Int) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d : Int) (p : Poly)
    : dvd_solve_elim_cert d₁ p₁ d₂ p₂ d p → d₁ ∣ p₁.denote' ctx → d₂ ∣ p₂.denote' ctx → d ∣ p.denote' ctx := by
  simp [dvd_solve_elim_cert]
  split <;> simp
  rename_i a₁ x₁ p₁ a₂ x₂ p₂
  intro _ hd _; subst x₁ p; simp [Int.neg_mul]
  intro h₁ h₂
  rw [Int.add_comm] at h₁ h₂
  rw [Int.add_neg_eq_sub]
  exact dvd_solve_elim' hd h₁ h₂

theorem dvd_norm (ctx : Context) (d : Int) (p₁ p₂ : Poly) : p₁.norm.beq' p₂ → d ∣ p₁.denote' ctx → d ∣ p₂.denote' ctx := by
  simp
  intro; subst p₂
  intro h₁
  simp [Poly.denote_norm ctx p₁, h₁]

theorem le_norm (ctx : Context) (p₁ p₂ : Poly) (h : p₁.norm.beq' p₂) : p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 := by
  simp at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  simp [*]

@[expose]
noncomputable def le_coeff_cert (p₁ p₂ : Poly) (k : Int) : Bool :=
  Int.blt' 0 k |>.and' (p₁.divCoeffs k |>.and' (p₂.beq' (p₁.div k)))

theorem le_coeff (ctx : Context) (p₁ p₂ : Poly) (k : Int) : le_coeff_cert p₁ p₂ k → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 := by
  simp [le_coeff_cert]
  intro h₁ h₂ h₃
  exact eq_of_norm_eq_of_divCoeffs h₁ h₂ h₃ |>.mp

@[expose]
noncomputable def le_neg_cert (p₁ p₂ : Poly) : Bool :=
  p₂.beq' (p₁.mul_k (-1) |>.addConst_k 1)

theorem le_neg (ctx : Context) (p₁ p₂ : Poly) : le_neg_cert p₁ p₂ → ¬ p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 := by
  simp [le_neg_cert]
  intro; subst p₂; simp; intro h
  replace h : _ + 1 ≤ -0 := Int.neg_lt_neg h
  simp at h
  exact h

@[expose]
def Poly.leadCoeff (p : Poly) : Int :=
  match p with
  | .add a _ _ => a
  | _ => 1

@[expose]
noncomputable def le_combine_cert (p₁ p₂ p₃ : Poly) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  p₃.beq' (p₁.combine_mul_k a₂ a₁ p₂)

theorem le_combine (ctx : Context) (p₁ p₂ p₃ : Poly)
    : le_combine_cert p₁ p₂ p₃ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [le_combine_cert]
  intro; subst p₃
  intro h₁ h₂; simp
  rw [← Int.add_zero 0]
  apply Int.add_le_add
  · rw [← Int.zero_mul (Poly.denote ctx p₂)]; apply Int.mul_le_mul_of_nonpos_right <;> simp [*]
  · rw [← Int.zero_mul (Poly.denote ctx p₁)]; apply Int.mul_le_mul_of_nonpos_right <;> simp [*]

@[expose]
noncomputable def le_combine_coeff_cert (p₁ p₂ p₃ : Poly) (k : Int) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  let p  := p₁.combine_mul_k a₂ a₁ p₂
  Int.blt' 0 k |>.and' (p.divCoeffs k |>.and' (p₃.beq' (p.div k)))

theorem le_combine_coeff (ctx : Context) (p₁ p₂ p₃ : Poly) (k : Int)
    : le_combine_coeff_cert p₁ p₂ p₃ k → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp only [le_combine_coeff_cert, Bool.and'_eq_and,
             Poly.beq'_eq, Bool.and_eq_true, and_imp]
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  generalize h : (p₁.combine_mul_k a₂ a₁ p₂) = p
  intro h₁ h₂ h₃ h₄ h₅
  have := le_combine ctx p₁ p₂ p
  simp only [le_combine_cert, Poly.beq'_eq] at this
  have aux₁ := this h.symm h₄ h₅
  have := le_coeff ctx p p₃ k
  simp only [le_coeff_cert, Bool.and'_eq_and, Poly.beq'_eq, Bool.and_eq_true, and_imp] at this
  exact this h₁ h₂ h₃ aux₁

theorem le_unsat (ctx : Context) (p : Poly) : p.isUnsatLe → p.denote' ctx ≤ 0 → False := by
  simp [Poly.isUnsatLe]; split <;> simp

theorem eq_norm (ctx : Context) (p₁ p₂ : Poly) (h : p₁.norm.beq' p₂) : p₁.denote' ctx = 0 → p₂.denote' ctx = 0 := by
  simp at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  simp [*]

@[expose]
noncomputable def eq_coeff_cert (p p' : Poly) (k : Int) : Bool :=
  p.beq' (p'.mul_k k) |>.and' (k > 0)

theorem eq_coeff (ctx : Context) (p p' : Poly) (k : Int) : eq_coeff_cert p p' k → p.denote' ctx = 0 → p'.denote' ctx = 0 := by
  simp [eq_coeff_cert]
  intro _ _; simp [mul_eq_zero_iff, *]

theorem eq_unsat (ctx : Context) (p : Poly) : p.isUnsatEq → p.denote' ctx = 0 → False := by
  simp [Poly.isUnsatEq] <;> split <;> simp

@[expose]
noncomputable def eq_unsat_coeff_cert (p : Poly) (k : Int) : Bool :=
  p.divCoeffs k |>.and' (Int.blt' 0 k |>.and' (cmod p.getConst k < 0))

theorem eq_unsat_coeff (ctx : Context) (p : Poly) (k : Int) : eq_unsat_coeff_cert p k → p.denote' ctx = 0 → False := by
  simp [eq_unsat_coeff_cert]
  intro h₁ h₂ h₃
  have h := poly_eq_zero_eq_false ctx h₁ h₂ h₃; clear h₁ h₂ h₃
  simp [h]

@[expose] def Poly.coeff (p : Poly) (x : Var) : Int :=
  match p with
  | .add a y p => bif x == y then a else coeff p x
  | .num _ => 0

@[expose] noncomputable def Poly.coeff_k (p : Poly) (x : Var) : Int :=
  Poly.rec (fun _ => 0) (fun a y _ ih => Bool.rec ih a (Nat.beq x y)) p

@[simp] theorem Poly.coeff_k_eq_coeff (p : Poly) (x : Var) : p.coeff_k x = p.coeff x := by
  induction p
  next => rfl
  next a y p ih =>
    simp [coeff_k, coeff, cond_eq_ite]; split
    next h => simp [h]
    next h => rw [← Nat.beq_eq, Bool.not_eq_true] at h; simp [h, ← ih]; rfl

private theorem eq_add_coeff_insert (ctx : Context) (p : Poly) (x : Var) : p.denote ctx = (p.coeff x) * (x.denote ctx) + (p.insert (-p.coeff x) x).denote ctx := by
  simp; rw [← Int.add_assoc, Int.neg_mul, Int.add_neg_cancel_right]

private theorem dvd_of_eq' {a x p : Int} : a*x + p = 0 → a ∣ p := by
  intro h
  replace h := Int.neg_eq_of_add_eq_zero h
  rw [Int.mul_comm, ← Int.neg_mul, Eq.comm, Int.mul_comm] at h
  exact ⟨-x, h⟩

@[expose]
def abs (x : Int) : Int :=
  Int.ofNat x.natAbs

private theorem abs_dvd {a p : Int} (h : a ∣ p) : abs a ∣ p := by
  cases a <;> simp [abs]
  · simp at h; assumption
  · simp [Int.negSucc_eq] at h; assumption

@[expose]
noncomputable def dvd_of_eq_cert (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) : Bool :=
  let a := p₁.coeff_k x
  d₂.beq' (abs a) |>.and' (p₂.beq' (p₁.insert (-a) x))

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

@[expose]
noncomputable def eq_dvd_subst_cert (x : Var) (p₁ : Poly) (d₂ : Int) (p₂ : Poly) (d₃ : Int) (p₃ : Poly) : Bool :=
  let a := p₁.coeff_k x
  let b := p₂.coeff_k x
  let p := p₁.insert (-a) x
  let q := p₂.insert (-b) x
  d₃.beq' (abs (a * d₂)) |>.and'
  (p₃.beq' (q.combine_mul_k a (-b) p))

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
  simp [this, Int.neg_mul]

-- TODO: delete after update stage0
@[expose] noncomputable def eq_eq_subst_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff_k x
  let b := p₂.coeff_k x
  p₃.beq' (p₁.combine_mul_k b (-a) p₂)

-- TODO: delete after update stage0
theorem eq_eq_subst (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_eq_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 → p₃.denote' ctx = 0 := by
  simp [eq_eq_subst_cert]
  intro; subst p₃
  intro h₁ h₂
  simp [*]

@[expose] noncomputable def eq_eq_subst'_cert (a b : Int) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  p₃.beq' (p₁.combine_mul_k b (-a) p₂)

theorem eq_eq_subst' (ctx : Context) (a b : Int) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_eq_subst'_cert a b p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 → p₃.denote' ctx = 0 := by
  simp [eq_eq_subst'_cert]
  intro; subst p₃
  intro h₁ h₂
  simp [*]

@[expose]
noncomputable def eq_le_subst_nonneg_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  Int.ble' 0 a |>.and' (p₃.beq' (p₂.combine_mul_k a (-b) p₁))

theorem eq_le_subst_nonneg (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_le_subst_nonneg_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [eq_le_subst_nonneg_cert]
  intro h
  intro; subst p₃
  intro h₁ h₂
  replace h₂ := Int.mul_le_mul_of_nonneg_left h₂ h
  simp at h₂
  simp [*]

@[expose]
noncomputable def eq_le_subst_nonpos_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  Int.ble' a 0 |>.and' (p₃.beq' (p₁.combine_mul_k b (-a) p₂))

theorem eq_le_subst_nonpos (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_le_subst_nonpos_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [eq_le_subst_nonpos_cert]
  intro h
  intro; subst p₃
  intro h₁ h₂
  simp [*, -Int.neg_nonpos_iff, Int.neg_mul]
  replace h₂ := Int.mul_le_mul_of_nonpos_left h₂ h; simp at h₂; clear h
  rw [Int.mul_comm]
  assumption

@[expose]
noncomputable def eq_of_core_cert (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  p₃.beq' (p₁.combine_mul_k 1 (-1) p₂)

theorem eq_of_core (ctx : Context) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_of_core_cert p₁ p₂ p₃ → p₁.denote' ctx = p₂.denote' ctx → p₃.denote' ctx = 0 := by
  simp [eq_of_core_cert]
  intro; subst p₃; simp
  intro h; rw [h, Int.add_neg_eq_sub, Int.sub_self]

@[expose] def Poly.isUnsatDiseq (p : Poly) : Bool :=
  match p with
  | .num 0 => true
  | _ => false

@[expose] noncomputable def Poly.isUnsatDiseq_k (p : Poly) : Bool :=
  Poly.rec (fun k => Int.beq' k 0) (fun _ _ _ _ => false) p

theorem diseq_norm (ctx : Context) (p₁ p₂ : Poly) (h : p₁.norm.beq' p₂) : p₁.denote' ctx ≠ 0 → p₂.denote' ctx ≠ 0 := by
  simp at h
  replace h := congrArg (Poly.denote ctx) h
  simp at h
  simp [*]

theorem diseq_coeff (ctx : Context) (p p' : Poly) (k : Int) : eq_coeff_cert p p' k → p.denote' ctx ≠ 0 → p'.denote' ctx ≠ 0 := by
  simp [eq_coeff_cert]
  intro _ _; simp [mul_eq_zero_iff, *]

theorem diseq_neg (ctx : Context) (p p' : Poly) : p'.beq' (p.mul (-1)) → p.denote' ctx ≠ 0 → p'.denote' ctx ≠ 0 := by
  simp; intro _ _; simp [*]

theorem diseq_unsat (ctx : Context) (p : Poly) : p.isUnsatDiseq_k → p.denote' ctx ≠ 0 → False := by
  simp [Poly.isUnsatDiseq_k] <;> cases p <;> simp

@[expose]
noncomputable def diseq_eq_subst_cert (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  !a.beq' 0 |>.and' (p₃.beq' (p₁.combine_mul_k b (-a) p₂))

theorem eq_diseq_subst (ctx : Context) (x : Var) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : diseq_eq_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≠ 0 → p₃.denote' ctx ≠ 0 := by
  simp [diseq_eq_subst_cert]
  intro _ _; subst p₃
  intro h₁ h₂
  simp [*]

theorem diseq_of_core (ctx : Context) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : eq_of_core_cert p₁ p₂ p₃ → p₁.denote' ctx ≠ p₂.denote' ctx → p₃.denote' ctx ≠ 0 := by
  simp [eq_of_core_cert]
  intro; subst p₃; simp
  intro h; rw [← Int.sub_eq_zero] at h
  rw [Int.add_neg_eq_sub]; assumption

@[expose]
noncomputable def eq_of_le_ge_cert (p₁ p₂ : Poly) : Bool :=
  p₂.beq' (p₁.mul_k (-1))

theorem eq_of_le_ge (ctx : Context) (p₁ : Poly) (p₂ : Poly)
    : eq_of_le_ge_cert p₁ p₂ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₁.denote' ctx = 0 := by
  simp [eq_of_le_ge_cert]
  intro; subst p₂; simp [-Int.neg_nonpos_iff]
  intro h₁ h₂
  simp [Int.eq_iff_le_and_ge, *]

@[expose]
noncomputable def le_of_le_diseq_cert (p₁ : Poly) (p₂ : Poly) (p₃ : Poly) : Bool :=
  -- Remark: we can generate two different certificates in the future, and avoid the `||` in the certificate.
  (p₂.beq' p₁ || p₂.beq' (p₁.mul_k (-1))).and'
  (p₃.beq' (p₁.addConst_k 1))

theorem le_of_le_diseq (ctx : Context) (p₁ : Poly) (p₂ : Poly) (p₃ : Poly)
    : le_of_le_diseq_cert p₁ p₂ p₃ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≠ 0 → p₃.denote' ctx ≤ 0 := by
  simp [le_of_le_diseq_cert]
  have (a : Int) : a ≤ 0 → ¬ a = 0 → 1 + a ≤ 0 := by
    intro h₁ h₂; cases (Int.lt_or_gt_of_ne h₂)
    next => apply Int.le_of_lt_add_one; rw [Int.add_comm, Int.add_lt_add_iff_right]; assumption
    next h => have := Int.lt_of_le_of_lt h₁ h; simp at this
  intro h; cases h <;> intro <;> subst p₂ p₃ <;> simp <;> apply this

@[expose]
noncomputable def diseq_split_cert (p₁ p₂ p₃ : Poly) : Bool :=
  p₂.beq' (p₁.addConst_k 1) |>.and'
  (p₃.beq' ((p₁.mul_k (-1)).addConst_k 1))

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

@[expose]
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

@[expose]
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
private theorem lcm_neg_left (a b : Int) : Int.lcm (-a) b = Int.lcm a b := by simp [Int.lcm]
private theorem lcm_neg_right (a b : Int) : Int.lcm a (-b) = Int.lcm a b := by simp [Int.lcm]
private theorem gcd_zero (a : Int) : Int.gcd a 0 = a.natAbs := by simp [Int.gcd]
private theorem lcm_one (a : Int) : Int.lcm a 1 = a.natAbs := by simp [Int.lcm]

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
  rw [Int.neg_ediv_of_dvd (Int.gcd_dvd_left ..)] at h₂
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

@[expose]
noncomputable def cooper_dvd_left_cert (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat) : Bool :=
  p₁.casesOn (fun _ => false) fun a x _ =>
  p₂.casesOn (fun _ => false) fun b y _ =>
  p₃.casesOn (fun _ => false) fun c z _ =>
   .and' (x.beq y) <| .and' (x.beq z) <|
   .and' (a < 0)  <| .and' (b > 0)  <|
   .and' (d > 0)  <| n.beq (Int.lcm a (a * d / Int.gcd (a * d) c))

@[expose]
def Poly.tail (p : Poly) : Poly :=
  match p with
  | .add _ _ p => p
  | _ => p

@[expose]
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
  rename_i a x p b y q c z s
  intro _ _; subst y z
  intro ha hb hd
  intro; subst n
  simp only [Poly.denote'_add, Poly.leadCoeff]
  intro h₁ h₂ h₃
  simp only [denote'_mul_combine_mul_addConst_eq]
  simp only [denote'_addConst_eq]
  exact cooper_dvd_left_core ha hb hd h₁ h₂ h₃

@[expose]
noncomputable def cooper_dvd_left_split_ineq_cert (p₁ p₂ : Poly) (k : Int) (b : Int) (p' : Poly) : Bool :=
  let p  := p₁.tail
  let q  := p₂.tail
  let a  := p₁.leadCoeff
  let p₁ := p.combine_mul_k b (-a) q
  p₂.leadCoeff.beq' b |>.and' (p'.beq' (p₁.addConst_k (b*k)))

theorem cooper_dvd_left_split_ineq (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (b : Int) (p' : Poly)
    : cooper_dvd_left_split ctx p₁ p₂ p₃ d k → cooper_dvd_left_split_ineq_cert p₁ p₂ k b p' → p'.denote' ctx ≤ 0 := by
  simp [cooper_dvd_left_split_ineq_cert, cooper_dvd_left_split]
  intros; subst p' b; simp; assumption

@[expose]
noncomputable def cooper_dvd_left_split_dvd1_cert (p₁ p' : Poly) (a : Int) (k : Int) : Bool :=
  a.beq' p₁.leadCoeff |>.and' (p'.beq' (p₁.tail.addConst_k k))

theorem cooper_dvd_left_split_dvd1 (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (a : Int) (p' : Poly)
    : cooper_dvd_left_split ctx p₁ p₂ p₃ d k → cooper_dvd_left_split_dvd1_cert p₁ p' a k → a ∣ p'.denote' ctx := by
  simp [cooper_dvd_left_split_dvd1_cert, cooper_dvd_left_split]
  intros; subst a p'; simp; assumption

@[expose]
noncomputable def cooper_dvd_left_split_dvd2_cert (p₁ p₃ : Poly) (d : Int) (k : Nat) (d' : Int) (p' : Poly): Bool :=
  let p  := p₁.tail
  let s  := p₃.tail
  let a  := p₁.leadCoeff
  let c  := p₃.leadCoeff
  let p₂ := p.combine_mul_k c (-a) s
  (d'.beq' (a*d)).and' (p'.beq' (p₂.addConst_k (c*k)))

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
    Int.zero_mul, Int.mul_zero, Int.add_zero, Int.dvd_zero,
    and_true] at h
  assumption

@[expose]
noncomputable def cooper_left_cert (p₁ p₂ : Poly) (n : Nat) : Bool :=
  p₁.casesOn (fun _ => false) fun a x _ =>
  p₂.casesOn (fun _ => false) fun b y _ =>
   .and' (x.beq y) <| .and' (a < 0)  <| .and' (b > 0)  <|
   n.beq a.natAbs

@[expose]
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
  rename_i a x p b y q
  intro; subst y
  intro ha hb
  intro; subst n
  simp only [Poly.denote'_add, Poly.leadCoeff]
  intro h₁ h₂
  have := cooper_left_core ha hb h₁ h₂
  simp only [denote'_mul_combine_mul_addConst_eq]
  simp only [denote'_addConst_eq]
  assumption

@[expose]
noncomputable def cooper_left_split_ineq_cert (p₁ p₂ : Poly) (k : Int) (b : Int) (p' : Poly) : Bool :=
  let p  := p₁.tail
  let q  := p₂.tail
  let a  := p₁.leadCoeff
  let p₁ := p.combine_mul_k b (-a) q
  p₂.leadCoeff.beq' b |>.and' (p'.beq' (p₁.addConst_k (b*k)))

theorem cooper_left_split_ineq (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (b : Int) (p' : Poly)
    : cooper_left_split ctx p₁ p₂ k → cooper_left_split_ineq_cert p₁ p₂ k b p' → p'.denote' ctx ≤ 0 := by
  simp [cooper_left_split_ineq_cert, cooper_left_split]
  intros; subst p' b; simp; assumption

@[expose]
noncomputable def cooper_left_split_dvd_cert (p₁ p' : Poly) (a : Int) (k : Int) : Bool :=
  a.beq' p₁.leadCoeff |>.and' (p'.beq' (p₁.tail.addConst_k k))

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
  simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg] at *
  apply orOver_of_exists
  have hlt := ofNat_lt h₁ h₂
  replace h₃ := Int.add_le_add_right h₃ (-(a*q)); rw [Int.add_right_neg] at h₃
  have : -(a * k) + b * p + -(a * q) = b * p + -(a * q) + -(a * k) := by ac_rfl
  rw [this] at h₃; clear this
  rw [Int.sub_neg, Int.add_comm] at h₄
  have : -(c * k) + -(c * q) + b * s = -(c * q) + b * s + -(c * k) := by ac_rfl
  rw [this] at h₅; clear this
  exists k.toNat
  simp only [hlt, and_true, cast_toNat h₁, h₃, h₄, h₅]

@[expose]
noncomputable def cooper_dvd_right_cert (p₁ p₂ p₃ : Poly) (d : Int) (n : Nat) : Bool :=
  p₁.casesOn (fun _ => false) fun a x _ =>
  p₂.casesOn (fun _ => false) fun b y _ =>
  p₃.casesOn (fun _ => false) fun c z _ =>
   .and (x.beq y) <| .and (x.beq z) <|
   .and (a < 0)  <| .and (b > 0)  <|
   .and (d > 0)  <| n.beq (Int.lcm b (b * d / Int.gcd (b * d) c))

@[expose]
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
  rename_i a x p b y q c z s
  intro _ _; subst y z
  intro ha hb hd
  intro; subst n
  simp only [Poly.denote'_add, Poly.leadCoeff]
  intro h₁ h₂ h₃
  have := cooper_dvd_right_core ha hb hd h₁ h₂ h₃
  simp only [denote'_mul_combine_mul_addConst_eq]
  simp only [denote'_addConst_eq]
  exact cooper_dvd_right_core ha hb hd h₁ h₂ h₃

@[expose]
noncomputable def cooper_dvd_right_split_ineq_cert (p₁ p₂ : Poly) (k : Int) (a : Int) (p' : Poly) : Bool :=
  let p  := p₁.tail
  let q  := p₂.tail
  let b  := p₂.leadCoeff
  let p₂ := p.combine_mul_k b (-a) q
  p₁.leadCoeff.beq' a |>.and' (p'.beq' (p₂.addConst_k ((-a)*k)))

theorem cooper_dvd_right_split_ineq (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (a : Int) (p' : Poly)
    : cooper_dvd_right_split ctx p₁ p₂ p₃ d k → cooper_dvd_right_split_ineq_cert p₁ p₂ k a p' → p'.denote' ctx ≤ 0 := by
  simp [cooper_dvd_right_split_ineq_cert, cooper_dvd_right_split]
  intros; subst a p'; simp; assumption

@[expose]
noncomputable def cooper_dvd_right_split_dvd1_cert (p₂ p' : Poly) (b : Int) (k : Int) : Bool :=
  b.beq' p₂.leadCoeff |>.and' (p'.beq' (p₂.tail.addConst_k k))

theorem cooper_dvd_right_split_dvd1 (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (k : Nat) (b : Int) (p' : Poly)
    : cooper_dvd_right_split ctx p₁ p₂ p₃ d k → cooper_dvd_right_split_dvd1_cert p₂ p' b k → b ∣ p'.denote' ctx := by
  simp [cooper_dvd_right_split_dvd1_cert, cooper_dvd_right_split]
  intros; subst b p'; simp; assumption

@[expose]
noncomputable def cooper_dvd_right_split_dvd2_cert (p₂ p₃ : Poly) (d : Int) (k : Nat) (d' : Int) (p' : Poly): Bool :=
  let q  := p₂.tail
  let s  := p₃.tail
  let b  := p₂.leadCoeff
  let c  := p₃.leadCoeff
  let p₂ := q.combine_mul_k (-c) b s
  d'.beq' (b*d) |>.and' (p'.beq' (p₂.addConst_k ((-c)*k)))

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
  simp only [Int.mul_one, gcd_zero, Int.natAbs_of_nonneg (Int.le_of_lt b_pos),
    Int.ediv_self (Int.ne_of_gt b_pos), lcm_one,
    Int.zero_mul, Int.mul_zero, Int.add_zero, Int.dvd_zero,
    and_true, Int.neg_zero] at h
  assumption

@[expose]
noncomputable def cooper_right_cert (p₁ p₂ : Poly) (n : Nat) : Bool :=
  p₁.casesOn (fun _ => false) fun a x _ =>
  p₂.casesOn (fun _ => false) fun b y _ =>
  .and' (x.beq y) <| .and' (a < 0)  <| .and' (b > 0) <| n.beq b.natAbs

@[expose]
def cooper_right_split (ctx : Context) (p₁ p₂ : Poly) (k : Nat) : Prop :=
  let p  := p₁.tail
  let q  := p₂.tail
  let a  := p₁.leadCoeff
  let b  := p₂.leadCoeff
  let p₁ := p.mul_k b |>.combine (q.mul_k (-a))
  (p₁.addConst ((-a)*k)).denote' ctx ≤ 0
  ∧ b ∣ (q.addConst k).denote' ctx

theorem cooper_right (ctx : Context) (p₁ p₂ : Poly) (n : Nat)
    : cooper_right_cert p₁ p₂ n
      → p₁.denote' ctx ≤ 0
      → p₂.denote' ctx ≤ 0
      → OrOver n (cooper_right_split ctx p₁ p₂) := by
  unfold cooper_right_split
  cases p₁ <;> cases p₂ <;> simp [cooper_right_cert, Poly.tail, -Poly.denote'_eq_denote]
  rename_i a x p b y q
  intro; subst y
  intro ha hb
  intro; subst n
  simp only [Poly.denote'_add, Poly.leadCoeff]
  intro h₁ h₂
  have := cooper_right_core ha hb h₁ h₂
  simp only [denote'_mul_combine_mul_addConst_eq]
  simp only [denote'_addConst_eq]
  assumption

@[expose]
noncomputable def cooper_right_split_ineq_cert (p₁ p₂ : Poly) (k : Int) (a : Int) (p' : Poly) : Bool :=
  let p  := p₁.tail
  let q  := p₂.tail
  let b  := p₂.leadCoeff
  let p₂ := p.combine_mul_k b (-a) q
  p₁.leadCoeff.beq' a |>.and' (p'.beq' (p₂.addConst_k ((-a)*k)))

theorem cooper_right_split_ineq (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (a : Int) (p' : Poly)
    : cooper_right_split ctx p₁ p₂ k → cooper_right_split_ineq_cert p₁ p₂ k a p' → p'.denote' ctx ≤ 0 := by
  simp [cooper_right_split_ineq_cert, cooper_right_split]
  intros; subst a p'; simp; assumption

@[expose]
noncomputable def cooper_right_split_dvd_cert (p₂ p' : Poly) (b : Int) (k : Int) : Bool :=
  b.beq' p₂.leadCoeff |>.and' (p'.beq' (p₂.tail.addConst_k k))

theorem cooper_right_split_dvd (ctx : Context) (p₁ p₂ : Poly) (k : Nat) (b : Int) (p' : Poly)
    : cooper_right_split ctx p₁ p₂ k → cooper_right_split_dvd_cert p₂ p' b k → b ∣ p'.denote' ctx := by
  simp [cooper_right_split_dvd_cert, cooper_right_split]
  intros; subst b p'; simp; assumption

private theorem one_emod_eq_one {a : Int} (h : a > 1) : 1 % a = 1 := by
  have aux₁ := Int.mul_ediv_add_emod 1 a
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
    conv => lhs; rw [← Int.mul_ediv_add_emod x d]
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

@[expose]
noncomputable def cooper_unsat_cert (p₁ p₂ p₃ : Poly) (d : Int) (α β : Int) : Bool :=
  p₁.casesOnAdd fun k₁ x p₁ =>
  p₂.casesOnAdd fun k₂ y p₂ =>
  p₃.casesOnAdd fun c z p₃ =>
  p₁.casesOnNum fun a =>
  p₂.casesOnNum fun b =>
  p₃.casesOnNum fun e =>
  (k₁.beq' (-1)) |>.and' (k₂.beq' 1) |>.and'
  (x.beq y) |>.and' (x.beq z) |>.and'
  (d > 1) |>.and' ((α * c + β * d).beq' 1) |>.and'
  (-b < cdiv (a - -α * e % d) d * d + -α * e % d)

theorem cooper_unsat (ctx : Context) (p₁ p₂ p₃ : Poly) (d : Int) (α β : Int)
   : cooper_unsat_cert p₁ p₂ p₃ d α β →
     p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → d ∣ p₃.denote' ctx → False := by
  unfold cooper_unsat_cert <;> cases p₁ <;> cases p₂ <;> cases p₃ <;> simp only [Poly.casesOnAdd,
    Bool.false_eq_true, Poly.denote'_add, false_implies]
  rename_i k₁ x p₁ k₂ y p₂ c z p₃
  cases p₁ <;> cases p₂ <;> cases p₃ <;> simp only [Poly.casesOnNum, Int.reduceNeg,
    Bool.and'_eq_and, Int.beq'_eq, Nat.beq_eq, Bool.and_eq_true, decide_eq_true_eq,
    and_imp, Bool.false_eq_true, false_implies, Poly.denote]
  rename_i a b e
  intro _ _ _ _; subst k₁ k₂ y z
  intro h₁ h₃ h₆; generalize Var.denote ctx x = x'
  intro h₄ h₅ h₂
  rw [Int.one_mul] at h₅
  exact cooper_unsat' h₁ h₂ h₃ h₄ h₅ h₆

theorem ediv_emod (x y : Int) : -1 * x + y * (x / y) + x % y = 0 := by
  rw [Int.add_assoc, Int.mul_ediv_add_emod x y, Int.add_comm]
  simp
  rw [Int.add_neg_eq_sub, Int.sub_self]

theorem emod_nonneg (x y : Int) : y != 0 → -1 * (x % y) ≤ 0 := by
  simp; intro h
  have := Int.neg_le_neg (Int.emod_nonneg x h)
  simp at this
  assumption

@[expose]
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

private theorem dvd_le_tight' {d p b₁ b₂ : Int} (hd : d > 0) (h₁ : d ∣ p + b₁) (h₂ : p + b₂ ≤ 0)
    : p + (b₁ - d*((b₁-b₂) / d)) ≤ 0 := by
  have ⟨k, h⟩ := h₁
  replace h₁ : p = d*k - b₁ := by
    replace h := congrArg (· - b₁) h
    simp only [Int.add_sub_cancel] at h
    assumption
  replace h₂ : d*k - b₁ + b₂ ≤ 0 := by
    rw [h₁] at h₂; assumption
  have : d*k ≤ b₁ - b₂ := by
    rw [Int.sub_eq_add_neg, Int.add_assoc, Lean.Omega.Int.add_le_zero_iff_le_neg,
        Int.neg_add, Int.neg_neg, Int.add_neg_eq_sub] at h₂
    assumption
  replace this : k ≤ (b₁ - b₂)/d := by
    rw [Int.mul_comm] at this; exact Int.le_ediv_of_mul_le hd this
  replace this := Int.mul_le_mul_of_nonneg_left this (Int.le_of_lt hd)
  rw [←h] at this
  replace this := Int.sub_nonpos_of_le this
  rw [Int.add_sub_assoc] at this
  exact this

private theorem eq_neg_addConst_add (ctx : Context) (p : Poly)
    : p.denote' ctx = (p.addConst (-p.getConst)).denote' ctx + p.getConst := by
  simp only [Poly.denote'_eq_denote, Poly.denote_addConst, Int.add_comm, Int.add_left_comm]
  rw [Int.add_right_neg]
  simp

@[expose]
noncomputable def dvd_le_tight_cert (d : Int) (p₁ p₂ p₃ : Poly) : Bool :=
  let b₁ := p₁.getConst
  let b₂ := p₂.getConst
  let p  := p₁.addConst_k (-b₁)
  Int.blt' 0 d |>.and' (p₂.beq' (p.addConst_k b₂) |>.and' (p₃.beq' (p.addConst_k (b₁ - d*((b₁ - b₂)/d)))))

theorem dvd_le_tight (ctx : Context) (d : Int) (p₁ p₂ p₃ : Poly)
    : dvd_le_tight_cert d p₁ p₂ p₃ → d ∣ p₁.denote' ctx → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp only [dvd_le_tight_cert, Bool.and'_eq_and, Poly.beq'_eq, Bool.and_eq_true,
             Poly.addConst_k_eq_addConst, Int.blt'_eq_true, and_imp]
  generalize p₂.getConst = b₂
  intro hd _ _; subst p₂ p₃
  have := eq_neg_addConst_add ctx p₁
  revert this
  generalize p₁.getConst = b₁
  generalize p₁.addConst (-b₁) = p
  intro h₁; rw [h₁]; clear h₁
  simp only [denote'_addConst_eq]
  simp only [Poly.denote'_eq_denote]
  exact dvd_le_tight' hd

@[expose]
noncomputable def dvd_neg_le_tight_cert (d : Int) (p₁ p₂ p₃ : Poly) : Bool :=
  let b₁ := p₁.getConst
  let b₂ := p₂.getConst
  let p  := p₁.addConst_k (-b₁)
  let b₁ := -b₁
  let p  := p.mul_k (-1)
  Int.blt' 0 d |>.and' (p₂.beq' (p.addConst_k b₂) |>.and' (p₃.beq' (p.addConst_k (b₁ - d*((b₁ - b₂)/d)))))

theorem Poly.mul_minus_one_getConst_eq (p : Poly) : (p.mul (-1)).getConst = -p.getConst := by
  simp [Poly.mul]
  induction p <;> simp [Poly.mul', Poly.getConst, *]

theorem dvd_neg_le_tight (ctx : Context) (d : Int) (p₁ p₂ p₃ : Poly)
    : dvd_neg_le_tight_cert d p₁ p₂ p₃ → d ∣ p₁.denote' ctx → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp only [dvd_neg_le_tight_cert, Poly.beq'_eq, Bool.and'_eq_and, Bool.and_eq_true,
             Int.blt'_eq_true, and_imp]
  generalize p₂.getConst = b₂
  intro hd _ _; subst p₂ p₃
  simp only [Poly.denote'_eq_denote, Int.reduceNeg, Poly.addConst_k_eq_addConst, Poly.denote_addConst, Poly.denote_mul, Poly.mul_k_eq_mul,
    Int.mul_add, Int.neg_mul, Int.one_mul, Int.mul_neg, Int.neg_neg, Int.add_comm, Int.add_assoc]
  intro h₁ h₂
  replace h₁ := Int.dvd_neg.mpr h₁
  have := eq_neg_addConst_add ctx (p₁.mul (-1))
  simp [Poly.mul_minus_one_getConst_eq] at this
  rw [← Int.add_assoc] at this
  rw [this] at h₁; clear this
  rw [← Int.add_assoc]
  revert h₁ h₂
  generalize -Poly.denote ctx p₁ + p₁.getConst = p
  generalize -p₁.getConst = b₁
  intro h₁ h₂; rw [Int.add_comm] at h₁
  exact dvd_le_tight' hd h₂ h₁

theorem le_norm_expr (ctx : Context) (lhs rhs : Expr) (p : Poly)
    : norm_eq_cert lhs rhs p → lhs.denote ctx ≤ rhs.denote ctx → p.denote' ctx ≤ 0 := by
  intro h₁ h₂; rwa [norm_le ctx lhs rhs p h₁] at h₂

@[expose]
noncomputable def not_le_norm_expr_cert (lhs rhs : Expr) (p : Poly) : Bool :=
  p.beq' ((((lhs.sub rhs).norm).mul_k (-1)).addConst_k 1)

theorem not_le_norm_expr (ctx : Context) (lhs rhs : Expr) (p : Poly)
    : not_le_norm_expr_cert lhs rhs p → ¬ lhs.denote ctx ≤ rhs.denote ctx → p.denote' ctx ≤ 0 := by
  simp [not_le_norm_expr_cert]
  intro; subst p; simp
  intro h
  replace h := Int.sub_nonpos_of_le h
  rw [Int.add_comm, Int.add_sub_assoc] at h
  rw [Int.neg_sub]; assumption

theorem dvd_norm_expr (ctx : Context) (d : Int) (e : Expr) (p : Poly)
    : p == e.norm → d ∣ e.denote ctx → d ∣ p.denote' ctx := by
  simp; intro; subst p; simp

theorem eq_norm_expr (ctx : Context) (lhs rhs : Expr) (p : Poly)
    : norm_eq_cert lhs rhs p → lhs.denote ctx = rhs.denote ctx → p.denote' ctx = 0 := by
  intro h₁ h₂; rwa [norm_eq ctx lhs rhs p h₁] at h₂

theorem not_eq_norm_expr (ctx : Context) (lhs rhs : Expr) (p : Poly)
    : norm_eq_cert lhs rhs p → ¬ lhs.denote ctx = rhs.denote ctx → ¬ p.denote' ctx = 0 := by
  simp [norm_eq_cert]
  intro; subst p; simp
  intro; rwa [Int.sub_eq_zero]

theorem of_not_dvd (a b : Int) : a != 0 → ¬ (a ∣ b) → b % a > 0 := by
  simp; intro h₁ h₂
  replace h₂ := Int.emod_pos_of_not_dvd h₂
  simp [h₁] at h₂
  assumption

@[expose]
noncomputable def eq_def_cert (x : Var) (xPoly : Poly) (p : Poly) : Bool :=
  p.beq' (.add (-1) x xPoly)

theorem eq_def (ctx : Context) (x : Var) (xPoly : Poly) (p : Poly)
    : eq_def_cert x xPoly p → x.denote ctx = xPoly.denote' ctx → p.denote' ctx = 0 := by
  simp [eq_def_cert]; intro _ h; subst p; simp [h]
  rw [← Int.sub_eq_add_neg, Int.sub_self]

theorem eq_def_norm (ctx : Context) (x : Var) (xPoly xPoly' : Poly) (p : Poly)
    : eq_def_cert x xPoly' p → x.denote ctx = xPoly.denote' ctx → xPoly.denote' ctx = xPoly'.denote' ctx → p.denote' ctx = 0 := by
  simp [eq_def_cert]; intro _ h₁ h₂; subst p; simp [h₁, h₂]
  rw [← Int.sub_eq_add_neg, Int.sub_self]

@[expose]
noncomputable def eq_def'_cert (x : Var) (e : Expr) (p : Poly) : Bool :=
  p.beq' (.add (-1) x e.norm)

theorem eq_def' (ctx : Context) (x : Var) (e : Expr) (p : Poly)
    : eq_def'_cert x e p → x.denote ctx = e.denote ctx → p.denote' ctx = 0 := by
  simp [eq_def'_cert]; intro _ h; subst p; simp [h]
  rw [← Int.sub_eq_add_neg, Int.sub_self]

@[expose]
noncomputable def eq_def'_norm_cert (x : Var) (e : Expr) (ePoly ePoly' p : Poly) : Bool :=
  ePoly.beq' e.norm |>.and' (p.beq' (.add (-1) x ePoly'))

theorem eq_def'_norm (ctx : Context) (x : Var) (e : Expr) (ePoly ePoly' : Poly) (p : Poly)
    : eq_def'_norm_cert x e ePoly ePoly' p → x.denote ctx = e.denote ctx → ePoly.denote' ctx = ePoly'.denote' ctx → p.denote' ctx = 0 := by
  simp [eq_def'_norm_cert]; intro _ _ h₁ h₂; subst ePoly p; simp [h₁, ← h₂]
  rw [← Int.sub_eq_add_neg, Int.sub_self]

theorem eq_norm_poly (ctx : Context) (p p' : Poly) : p.denote' ctx = p'.denote' ctx → p.denote' ctx = 0 → p'.denote' ctx = 0 := by
  intro h; rw [h]; simp

theorem le_norm_poly (ctx : Context) (p p' : Poly) : p.denote' ctx = p'.denote' ctx → p.denote' ctx ≤ 0 → p'.denote' ctx ≤ 0 := by
  intro h; rw [h]; simp

theorem diseq_norm_poly (ctx : Context) (p p' : Poly) : p.denote' ctx = p'.denote' ctx → p.denote' ctx ≠ 0 → p'.denote' ctx ≠ 0 := by
  intro h; rw [h]; simp

theorem dvd_norm_poly (ctx : Context) (d : Int) (p p' : Poly) : p.denote' ctx = p'.denote' ctx → d ∣ p.denote' ctx → d ∣ p'.denote' ctx := by
  intro h; rw [h]; simp

/-!
Constraint propagation helper theorems.
-/

@[expose]
def le_of_le_cert (p₁ p₂ : Poly) : Bool :=
  match p₁, p₂ with
  | .add .., .num _ => false
  | .num _, .add .. => false
  | .num c₁, .num c₂ => c₁ ≥ c₂
  | .add a₁ x₁ p₁, .add a₂ x₂ p₂ => a₁ == a₂ && x₁ == x₂ && le_of_le_cert p₁ p₂

theorem le_of_le' (ctx : Context) (p₁ p₂ : Poly) : le_of_le_cert p₁ p₂ → ∀ k, p₁.denote' ctx ≤ k → p₂.denote' ctx ≤ k := by
  simp [Poly.denote'_eq_denote]
  fun_induction le_of_le_cert <;> simp [Poly.denote]
  next c₁ c₂ =>
    intro h k h₁
    exact Int.le_trans h h₁
  next a₁ x₁ p₁ a₂ x₂ p₂ ih =>
    intro _ _ h; subst a₁ x₁
    replace ih := ih h; clear h
    intro k h
    replace h : p₁.denote ctx ≤ k - a₂ * x₂.denote ctx := by omega
    replace ih := ih _ h
    omega

theorem le_of_le (ctx : Context) (p₁ p₂ : Poly) : le_of_le_cert p₁ p₂ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 :=
  fun h => le_of_le' ctx p₁ p₂ h 0

@[expose]
def not_le_of_le_cert (p₁ p₂ : Poly) : Bool :=
  match p₁, p₂ with
  | .add .., .num _ => false
  | .num _, .add .. => false
  | .num c₁, .num c₂ => c₁ ≥ 1 - c₂
  | .add a₁ x₁ p₁, .add a₂ x₂ p₂ => a₁ == -a₂ && x₁ == x₂ && not_le_of_le_cert p₁ p₂

theorem not_le_of_le' (ctx : Context) (p₁ p₂ : Poly) : not_le_of_le_cert p₁ p₂ → ∀ k, p₁.denote' ctx ≤ k → ¬ (p₂.denote' ctx ≤ -k) := by
  simp [Poly.denote'_eq_denote]
  fun_induction not_le_of_le_cert <;> simp [Poly.denote]
  next c₁ c₂ =>
    intro h k h₁
    omega
  next a₁ x₁ p₁ a₂ x₂ p₂ ih =>
    intro _ _ h; subst a₁ x₁
    replace ih := ih h; clear h
    intro k h
    replace h : p₁.denote ctx ≤ k + a₂ * x₂.denote ctx := by rw [Int.neg_mul] at h; omega
    replace ih := ih _ h
    omega

theorem not_le_of_le (ctx : Context) (p₁ p₂ : Poly) : not_le_of_le_cert p₁ p₂ → p₁.denote' ctx ≤ 0 → ¬ (p₂.denote' ctx ≤ 0) := by
  intro h h₁
  have := not_le_of_le' ctx p₁ p₂ h 0 h₁; simp at this
  simp [*]

theorem natCast_sub (x y : Nat)
    : (NatCast.natCast (x - y) : Int)
      =
      if (NatCast.natCast y : Int) + (-1)*NatCast.natCast x ≤ 0 then
        (NatCast.natCast x : Int) + -1*NatCast.natCast y
      else
        (0 : Int) := by
  change (↑(x - y) : Int) = if (↑y : Int) + (-1)*↑x ≤ 0 then (↑x : Int) + (-1)*↑y else 0
  rw [Int.neg_mul, ← Int.sub_eq_add_neg, Int.one_mul]
  rw [Int.neg_mul, ← Int.sub_eq_add_neg, Int.one_mul]
  split
  next h =>
    replace h := Int.le_of_sub_nonpos h
    rw [Int.ofNat_le] at h
    rw [Int.ofNat_sub h]
  next h =>
    have : ¬ (↑y : Int) ≤ ↑x := by
      intro h
      replace h := Int.sub_nonpos_of_le h
      contradiction
    rw [Int.ofNat_le] at this
    rw [Lean.Omega.Int.ofNat_sub_eq_zero this]

/-! Helper theorem for linearizing nonlinear terms -/

@[expose] noncomputable def var_eq_cert (x : Var) (k : Int) (p : Poly) : Bool :=
  Poly.rec (fun _ => false)
    (fun k₁ x' p' _ => Poly.rec (fun k₂ => k₁ != 0 && x == x' && k == -k₂/k₁) (fun _ _ _ _ => false) p')
    p

theorem var_eq (ctx : Context) (x : Var) (k : Int) (p : Poly) : var_eq_cert x k p → p.denote' ctx = 0 → x.denote ctx = k := by
  simp [var_eq_cert]; cases p <;> simp; next k₁ x' p' =>
  cases p' <;> simp; next k₂ =>
  intro h₁ _ _; subst x' k; intro h₂
  replace h₂ := Int.neg_eq_of_add_eq_zero h₂
  rw [Int.neg_eq_comm] at h₂
  rw [← h₂]; clear h₂; simp; rw [Int.mul_comm, Int.mul_ediv_cancel]
  assumption

@[expose] noncomputable def of_var_eq_mul_cert (x : Var) (k : Int) (y : Var) (p : Poly) : Bool :=
  p.beq' (.add 1 x (.add (-k) y (.num 0)))

theorem of_var_eq_mul (ctx : Context) (x : Var) (k : Int) (y : Var) (p : Poly) : of_var_eq_mul_cert x k y p → x.denote ctx = k * y.denote ctx → p.denote' ctx = 0 := by
  simp [of_var_eq_mul_cert]; intro _ h; subst p; simp [h]
  rw [Int.neg_mul, ← Int.sub_eq_add_neg, Int.sub_self]

@[expose] noncomputable def of_var_eq_var_cert (x : Var) (y : Var) (p : Poly) : Bool :=
  p.beq' (.add 1 x (.add (-1) y (.num 0)))

theorem of_var_eq_var (ctx : Context) (x : Var) (y : Var) (p : Poly) : of_var_eq_var_cert x y p → x.denote ctx = y.denote ctx → p.denote' ctx = 0 := by
  simp [of_var_eq_var_cert]; intro _ h; subst p; simp [h]
  rw [← Int.sub_eq_add_neg, Int.sub_self]

@[expose] noncomputable def of_var_eq_cert (x : Var) (k : Int) (p : Poly) : Bool :=
  p.beq' (.add 1 x (.num (-k)))

theorem of_var_eq (ctx : Context) (x : Var) (k : Int) (p : Poly) : of_var_eq_cert x k p → x.denote ctx = k → p.denote' ctx = 0 := by
  simp [of_var_eq_cert]; intro _ h; subst p; simp [h]
  rw [← Int.sub_eq_add_neg, Int.sub_self]

theorem eq_one_mul (a : Int) : a = 1*a := by simp
theorem mul_eq_kk (a b k₁ k₂ k : Int) (h₁ : a = k₁) (h₂ : b = k₂) (h₃ : k₁*k₂ == k) : a*b = k := by simp_all
theorem mul_eq_kkx (a b k₁ k₂ c k : Int) (h₁ : a = k₁) (h₂ : b = k₂*c) (h₃ : k₁*k₂ == k) : a*b = k*c := by
  simp at h₃; rw [h₁, h₂, ← Int.mul_assoc, h₃]
theorem mul_eq_kxk (a b k₁ c k₂ k : Int) (h₁ : a = k₁*c) (h₂ : b = k₂) (h₃ : k₁*k₂ == k) : a*b = k*c := by
  simp at h₃; rw [h₁, h₂, Int.mul_comm, ← Int.mul_assoc, Int.mul_comm k₂, h₃]
theorem mul_eq_zero_left (a b : Int) (h : a = 0) : a*b = 0 := by simp [*]
theorem mul_eq_zero_right (a b : Int) (h : b = 0) : a*b = 0 := by simp [*]

theorem div_eq (a b k : Int) (h : b = k) : a / b = a / k := by simp [*]
theorem mod_eq (a b k : Int) (h : b = k) : a % b = a % k := by simp [*]

theorem div_eq' (a b b' k : Int) (h₁ : b = b') (h₂ : k == a/b') : a / b = k := by simp_all
theorem mod_eq' (a b b' k : Int) (h₁ : b = b') (h₂ : k == a%b') : a % b = k := by simp_all

theorem pow_eq (a : Int) (b : Nat) (a' b' k : Int) (h₁ : a = a') (h₂ : ↑b = b') (h₃ : k == a'^b'.toNat) : a^b = k := by
  simp [← h₁, ← h₂] at h₃; simp [h₃]

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
