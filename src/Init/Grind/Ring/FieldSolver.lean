/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.CommSolver
public import Init.Grind.Ordered.Field
public import Init.Data.Nat.Gcd
import Init.LawfulBEqTactics
import Init.Data.Nat.Lemmas
import Init.Omega
import Init.Data.Nat.MinMax
import Init.Data.Bool

@[expose] public section

namespace Lean.Grind.CommRing
open Std
attribute [local instance] Semiring.natCast Ring.intCast

/-!
# Numeral inverses as rational coefficients

In a field of characteristic zero, the inverse `c⁻¹` of a numeral `c ≠ 0` is not an atom of the
polynomial normal form: `a / 2 + a / 2` must normalize to `a`. The reflection language `Expr`
denotes into any ring and has no inverse, so `c⁻¹` is reified as a variable `x` and the
`InvVars` list records `x ↦ c`. The integer polynomial of the term is then normalized into a
`PolyQ` `num / den`: an integer polynomial `num` over the remaining variables and a
denominator `den`, in lowest terms. Every `x` is eliminated with `Poly.cancelVar`, which is
justified by `c * x = 1`; that equation holds because `c ≠ 0` in characteristic zero.

The side condition `InvVars.ok` (each recorded variable denotes the inverse of its numeral) is
an equation between two lists that the kernel checks by `rfl`, since the context holds the
inverse terms themselves.

The inverse `x⁻¹` of an atom `x` is a variable `y` as well. When `x ≠ 0` is known, `x * y = 1`
and every monomial containing both `x` and `y` is reduced (`Poly.cancelInv`); `InvAtoms`
records the pairs `(y, x)` and `InvAtoms.ok` holds their equations, which are proved from
`x ≠ 0`. This needs no characteristic: `Expr.eq_of_cancelInvs_eq` and the `normA` relation
certificates work in any `CommRing`, and `toPolyQ` combines both kinds of inverses.
-/

/-- Variables that denote inverses of numerals: `(x, c)` records that `x` denotes `(OfNat.ofNat c)⁻¹`. -/
abbrev InvVars := List (Var × Nat)

/-- A polynomial with a denominator, denoting `num.denote ctx * (den : α)⁻¹`. -/
structure PolyQ where
  num : Poly
  den : Nat
  deriving BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def InvVars.denoteVars (ctx : Context α) (invs : InvVars) : List α :=
  invs.map fun p => p.1.denote ctx

def InvVars.denoteInvs [Field α] (invs : InvVars) : List α :=
  invs.map fun p => (OfNat.ofNat (α := α) p.2)⁻¹

/-- Each variable recorded in `invs` denotes the inverse of its numeral. -/
def InvVars.ok [Field α] (ctx : Context α) (invs : InvVars) : Prop :=
  invs.denoteVars ctx = invs.denoteInvs

theorem InvVars.ok_cons [Field α] (ctx : Context α) (x : Var) (c : Nat) (invs : InvVars) :
    InvVars.ok ctx ((x, c) :: invs) ↔ x.denote ctx = (OfNat.ofNat (α := α) c)⁻¹ ∧ InvVars.ok ctx invs := by
  simp [ok, denoteVars, denoteInvs]

/-! ## Inverses of atoms -/

theorem Mon.degreeOf_cancelVar (m : Mon) (x y : Var) (h : x ≠ y) : (m.cancelVar x).degreeOf y = m.degreeOf y := by
  induction m with
  | unit => rfl
  | mult pw m ih =>
    simp only [cancelVar, cond_eq_ite]
    split
    next h' => simp only [beq_iff_eq] at h'; subst h'; simp [degreeOf, h]
    next => simp [degreeOf, ih]

/--
Cancels `x ^ d * y ^ d` from `m`, where `d` is the smaller of the degrees of `x` and `y` in `m`.
Justified by `x * y = 1`; a no-op when `x = y`.
-/
def Mon.cancelInv (x y : Var) (m : Mon) : Mon :=
  let a := m.degreeOf x
  let b := m.degreeOf y
  bif x == y || a == 0 || b == 0 then m else
  let m' := (m.cancelVar x).cancelVar y
  bif a < b then m'.mulPow { x := y, k := b - a }
  else bif b < a then m'.mulPow { x, k := a - b }
  else m'

private theorem pow_mul_pow_of_le [CommSemiring α] {u v : α} (h : u * v = 1) {a b : Nat} (hab : a ≤ b) :
    u ^ a * v ^ b = v ^ (b - a) := by
  have : b = (b - a) + a := (Nat.sub_add_cancel hab).symm
  rw [this, Semiring.pow_add, Nat.add_sub_cancel, CommSemiring.mul_comm (v ^ (b - a)), ← Semiring.mul_assoc,
    ← CommSemiring.mul_pow, h, Semiring.one_pow, Semiring.one_mul]

theorem Mon.denote_cancelInv [CommSemiring α] (ctx : Context α) (m : Mon) (x y : Var)
    (h : x.denote ctx * y.denote ctx = 1) : (m.cancelInv x y).denote ctx = m.denote ctx := by
  simp only [cancelInv, cond_eq_ite]
  split
  next => rfl
  next hne =>
    have hxy : x ≠ y := fun h' => hne (by simp [h'])
    have hm : m.denote ctx = x.denote ctx ^ m.degreeOf x * (y.denote ctx ^ m.degreeOf y * ((m.cancelVar x).cancelVar y).denote ctx) := by
      rw [Mon.denote_cancelVar ctx m x, Mon.denote_cancelVar ctx (m.cancelVar x) y, Mon.degreeOf_cancelVar m x y hxy]
    rw [hm, ← Semiring.mul_assoc]
    simp only [decide_eq_true_eq]
    split
    next hlt =>
      rw [Mon.denote_mulPow, Power.denote_eq, pow_mul_pow_of_le h (Nat.le_of_lt hlt)]
    next hnlt =>
      split
      next hlt =>
        rw [Mon.denote_mulPow, Power.denote_eq, CommSemiring.mul_comm (x.denote ctx ^ m.degreeOf x),
          pow_mul_pow_of_le (by rw [CommSemiring.mul_comm]; exact h) (Nat.le_of_lt hlt)]
      next hnlt' =>
        have heq : m.degreeOf x = m.degreeOf y := Nat.le_antisymm (Nat.le_of_not_lt hnlt') (Nat.le_of_not_lt hnlt)
        rw [heq, ← CommSemiring.mul_pow, h, Semiring.one_pow, Semiring.one_mul]

/-- Cancels `x ^ d * y ^ d` from every monomial of `p` (`Mon.cancelInv`). -/
def Poly.cancelInv (x y : Var) (p : Poly) : Poly :=
  go p (.num 0)
where
  go : Poly → Poly → Poly
    | .num k, acc => acc.addConst k
    | .add k m p, acc => go p (acc.insert k (m.cancelInv x y))

theorem Poly.denote_cancelInv [CommRing α] (ctx : Context α) (p : Poly) (x y : Var)
    (h : x.denote ctx * y.denote ctx = 1) : (p.cancelInv x y).denote ctx = p.denote ctx := by
  suffices ∀ acc, (cancelInv.go x y p acc).denote ctx = p.denote ctx + acc.denote ctx by
    rw [cancelInv, this, denote, Ring.intCast_zero, Semiring.add_zero]
  intro acc
  induction p generalizing acc with
  | num k => simp [cancelInv.go, denote_addConst, denote, Semiring.add_comm]
  | add k m p ih =>
    simp only [cancelInv.go]
    rw [ih, denote_insert, Mon.denote_cancelInv ctx _ x y h]
    simp only [denote, Ring.zsmul_eq_intCast_mul]
    rw [← Semiring.add_assoc, Semiring.add_comm (denote ctx p), Semiring.add_assoc]

/-- Variables that denote inverses of variables: `(y, x)` records that `y` denotes `x⁻¹`, for `x ≠ 0`. -/
abbrev InvAtoms := List (Var × Var)

/-- `x.denote ctx * y.denote ctx = 1` for each `(y, x)`. -/
def InvAtoms.ok [Ring α] (ctx : Context α) : InvAtoms → Prop
  | [] => True
  | (y, x) :: l => x.denote ctx * y.denote ctx = 1 ∧ ok ctx l

theorem InvAtoms.ok_cons [Ring α] (ctx : Context α) (y x : Var) (l : InvAtoms)
    (h₁ : x.denote ctx * y.denote ctx = 1) (h₂ : ok ctx l) : ok ctx ((y, x) :: l) :=
  ⟨h₁, h₂⟩

def Poly.cancelInvs (p : Poly) (ainvs : InvAtoms) : Poly :=
  ainvs.foldl (fun p yx => p.cancelInv yx.2 yx.1) p

theorem Poly.denote_cancelInvs [CommRing α] (ctx : Context α) (p : Poly) (ainvs : InvAtoms)
    (h : ainvs.ok ctx) : (p.cancelInvs ainvs).denote ctx = p.denote ctx := by
  induction ainvs generalizing p with
  | nil => rfl
  | cons yx l ih =>
    simp only [cancelInvs, List.foldl_cons] at *
    rw [ih _ h.2, Poly.denote_cancelInv _ _ _ _ h.1]

/-! Kernel-reduction variants for inverse cancellation. -/

noncomputable def Mon.mulPow_k (pw : Power) (m : Mon) : Mon :=
  Mon.rec (.mult pw .unit)
    (fun pw' m ih => Bool.rec
      (Bool.rec (.mult {x := pw.x, k := Nat.add pw.k pw'.k} m) (.mult pw' ih) (Nat.blt pw'.x pw.x))
      (.mult pw (.mult pw' m)) (Nat.blt pw.x pw'.x)) m

noncomputable def Mon.cancelInv_k (x y : Var) (m : Mon) : Mon :=
  let a := Mon.degreeOf_k m x
  let b := Mon.degreeOf_k m y
  let m' := Mon.cancelVar_k (Mon.cancelVar_k m x) y
  Bool.rec
    (Bool.rec
      (Bool.rec
        (Bool.rec (Bool.rec m' (Mon.mulPow_k ⟨x, Nat.sub a b⟩ m') (Nat.blt b a))
          (Mon.mulPow_k ⟨y, Nat.sub b a⟩ m') (Nat.blt a b))
        m (Nat.beq b 0))
      m (Nat.beq a 0))
    m (Nat.beq x y)

noncomputable def Poly.cancelInv_k (x y : Var) (p : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k acc => acc.addConst_k k)
    (fun k m _ ih acc => ih (acc.insert_k k (Mon.cancelInv_k x y m))) p (.num 0)

noncomputable def Poly.cancelInvs_k (p : Poly) (invs : InvAtoms) : Poly :=
  List.rec (motive := fun _ => Poly → Poly) (fun p => p)
    (fun yx _ ih p => ih (Poly.cancelInv_k yx.2 yx.1 p)) invs p

@[simp] theorem Mon.mulPow_k_eq_mulPow (pw : Power) (m : Mon) : Mon.mulPow_k pw m = m.mulPow pw := by
  induction m with
  | unit => rfl
  | mult pw' m ih =>
    change Bool.rec (motive := fun _ => Mon)
      (Bool.rec (.mult {x := pw.x, k := Nat.add pw.k pw'.k} m) (.mult pw' (Mon.mulPow_k pw m)) (Nat.blt pw'.x pw.x))
      (.mult pw (.mult pw' m)) (Nat.blt pw.x pw'.x) = _
    rw [ih]
    simp only [Mon.mulPow, Bool.rec_eq, cond_eq_ite, Power.varLt]
    rfl

@[simp] theorem Mon.cancelInv_k_eq_cancelInv (x y : Var) (m : Mon) : Mon.cancelInv_k x y m = m.cancelInv x y := by
  simp only [Mon.cancelInv_k, Mon.degreeOf_k_eq_degreeOf, Mon.cancelVar_k_eq_cancelVar, Mon.mulPow_k_eq_mulPow, Bool.rec_eq,
    Mon.cancelInv, cond_eq_ite, Bool.or_eq_true, Nat.beq_eq_true_eq, Nat.beq_eq, Nat.blt_eq, decide_eq_true_eq]
  split <;> simp_all
  split <;> simp_all

@[simp] theorem Poly.cancelInv_k_eq_cancelInv (x y : Var) (p : Poly) : Poly.cancelInv_k x y p = p.cancelInv x y := by
  suffices h : ∀ acc, Poly.rec (motive := fun _ => Poly → Poly)
      (fun k acc => acc.addConst_k k)
      (fun k m _ ih acc => ih (acc.insert_k k (Mon.cancelInv_k x y m))) p acc = Poly.cancelInv.go x y p acc by
    exact h (.num 0)
  induction p with
  | num k => intro acc; simp [Poly.cancelInv.go]
  | add k m p ih => intro acc; simp only [Poly.cancelInv.go, ← ih, Poly.insert_k_eq_insert, Mon.cancelInv_k_eq_cancelInv]

@[simp] theorem Poly.cancelInvs_k_eq_cancelInvs (p : Poly) (invs : InvAtoms) : Poly.cancelInvs_k p invs = p.cancelInvs invs := by
  induction invs generalizing p with
  | nil => rfl
  | cons yx l ih =>
    change Poly.cancelInvs_k (Poly.cancelInv_k yx.2 yx.1 p) l = _
    rw [ih, Poly.cancelInv_k_eq_cancelInv]
    rfl

/-! ## Inverses of numerals -/

def PolyQ.denote [Field α] (ctx : Context α) (q : PolyQ) : α :=
  q.num.denote ctx * (q.den : α)⁻¹

/--
Eliminates the variable `x`, which denotes `c⁻¹`, from `p`: the polynomial is multiplied by
`c ^ n`, where `n` is the maximal degree of `x` in `p`, so that every power `x ^ k` can be
cancelled against the coefficient (`c ^ k * x ^ k = 1`); the denominator is `c ^ n`.
`c = 0` is not an inverse and is left alone.
-/
def Poly.substInv (p : Poly) (x : Var) (c : Nat) : PolyQ :=
  bif c == 0 then ⟨p, 1⟩ else
  let n := p.maxDegreeOf x
  ⟨(p.mulConst ((c ^ n : Nat) : Int)).cancelVar (c : Int) x, c ^ n⟩

def PolyQ.substInv (q : PolyQ) (x : Var) (c : Nat) : PolyQ :=
  let q' := q.num.substInv x c
  ⟨q'.num, q.den * q'.den⟩

/--
Lowest terms: divides `num` and `den` by their greatest common factor. The divisions are
checked by multiplying back, so the correctness proof needs no divisibility reasoning.
-/
def PolyQ.reduce (q : PolyQ) : PolyQ :=
  let g := Nat.gcd q.num.gcdCoeffs q.den
  bif g ≤ 1 then q else
  let num := q.num.divConst g
  let den := q.den / g
  bif num.mulConst g == q.num && den * g == q.den then ⟨num, den⟩ else q

/--
Cancels the inverse pairs of `ainvs`, eliminates the numeral inverses of `invs`, and reduces
the result to lowest terms.
-/
def Poly.toPolyQ (p : Poly) (invs : InvVars) (ainvs : InvAtoms) : PolyQ :=
  (invs.foldl (fun (q : PolyQ) xc => q.substInv xc.1 xc.2) ⟨p.cancelInvs ainvs, 1⟩).reduce

/-! Kernel-reduction variants of the functions used by `Poly.toPolyQ`. -/

noncomputable def Poly.maxDegreeOf_k (p : Poly) (x : Var) : Nat :=
  Poly.rec (motive := fun _ => Nat → Nat) (fun _ acc => acc)
    (fun _ m _ ih acc => ih (Bool.rec acc (Mon.degreeOf_k m x) (Nat.ble acc (Mon.degreeOf_k m x)))) p 0

theorem Poly.maxDegreeOf_k_eq (p : Poly) (x : Var) : p.maxDegreeOf_k x = p.maxDegreeOf x := by
  suffices h : ∀ acc, Poly.rec (motive := fun _ => Nat → Nat) (fun _ acc => acc)
      (fun _ m _ ih acc => ih (Bool.rec acc (Mon.degreeOf_k m x) (Nat.ble acc (Mon.degreeOf_k m x)))) p acc
      = Poly.maxDegreeOf.go x p acc by exact h 0
  induction p with
  | num k => intro acc; rfl
  | add k m p ih =>
    intro acc
    show Poly.rec (motive := fun _ => Nat → Nat) _ _ p _ = _
    rw [ih, Mon.degreeOf_k_eq_degreeOf]
    simp only [Poly.maxDegreeOf.go]
    congr 1
    cases h : Nat.ble acc (m.degreeOf x)
    · have : ¬ acc ≤ m.degreeOf x := by rw [← Nat.ble_eq]; simp [h]
      show acc = Nat.max acc (m.degreeOf x); exact (Nat.max_eq_left (Nat.le_of_lt (Nat.not_le.mp this))).symm
    · have : acc ≤ m.degreeOf x := by rw [← Nat.ble_eq]; exact h
      show m.degreeOf x = Nat.max acc (m.degreeOf x); exact (Nat.max_eq_right this).symm

noncomputable def Poly.gcdCoeffs_k.go (p : Poly) : Nat → Nat :=
  Poly.rec (motive := fun _ => Nat → Nat)
    (fun k acc => Bool.rec (Nat.gcd acc (Int.natAbs_k k)) acc (Nat.beq acc 1))
    (fun k _ _ ih acc => Bool.rec (ih (Nat.gcd acc (Int.natAbs_k k))) acc (Nat.beq acc 1)) p

noncomputable def Poly.gcdCoeffs_k (p : Poly) : Nat :=
  Poly.rec (fun k => Int.natAbs_k k) (fun k _ p _ => Poly.gcdCoeffs_k.go p (Int.natAbs_k k)) p

theorem Poly.gcdCoeffs_k_eq (p : Poly) : p.gcdCoeffs_k = p.gcdCoeffs := by
  have hgo : ∀ p acc, Poly.gcdCoeffs_k.go p acc = Poly.gcdCoeffs.go p acc := by
    intro p
    induction p with
    | num k =>
      intro acc
      show Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq acc 1) = _
      unfold Poly.gcdCoeffs.go
      cases h : Nat.beq acc 1
      · have : (acc == 1) = false := h
        simp [this]
      · have : (acc == 1) = true := h
        simp [this]
    | add k m p ih =>
      intro acc
      show Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq acc 1) = _
      unfold Poly.gcdCoeffs.go
      cases h : Nat.beq acc 1
      · have : (acc == 1) = false := h
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        show Poly.gcdCoeffs_k.go p _ = _
        rw [ih]; simp
      · have : (acc == 1) = true := h
        simp [this]
  cases p with
  | num k => simp [gcdCoeffs_k, gcdCoeffs]
  | add k m p => show Poly.gcdCoeffs_k.go p (Int.natAbs_k k) = _; rw [hgo]; simp [gcdCoeffs]

noncomputable def Poly.divConst_k (p : Poly) (a : Int) : Poly :=
  Poly.rec (fun k => .num (Int.ediv_k k a)) (fun k m _ ih => .add (Int.ediv_k k a) m ih) p

theorem Poly.divConst_k_eq (p : Poly) (a : Int) : p.divConst_k a = p.divConst a := by
  induction p with
  | num k => simp [divConst_k, divConst]
  | add k m p ih => show Poly.add _ m (p.divConst_k a) = _; rw [ih]; simp [divConst]

noncomputable def Poly.substInv_k (p : Poly) (x : Var) (c : Nat) : PolyQ :=
  Bool.rec
    ⟨(p.mulConst_k (Int.ofNat (Nat.pow c (p.maxDegreeOf_k x)))).cancelVar_k (Int.ofNat c) x, Nat.pow c (p.maxDegreeOf_k x)⟩
    ⟨p, 1⟩ (Nat.beq c 0)

theorem Poly.substInv_k_eq (p : Poly) (x : Var) (c : Nat) : p.substInv_k x c = p.substInv x c := by
  unfold substInv_k substInv
  cases h : Nat.beq c 0
  · have : (c == 0) = false := h
    simp only [this, Bool.cond_false]
    rw [Poly.maxDegreeOf_k_eq, Poly.mulConst_k_eq_mulConst, Poly.cancelVar_k_eq]; rfl
  · have : (c == 0) = true := h
    simp only [this, Bool.cond_true]

noncomputable def PolyQ.substInv_k (q : PolyQ) (x : Var) (c : Nat) : PolyQ :=
  ⟨(q.num.substInv_k x c).num, Nat.mul q.den (q.num.substInv_k x c).den⟩

theorem PolyQ.substInv_k_eq (q : PolyQ) (x : Var) (c : Nat) : q.substInv_k x c = q.substInv x c := by
  unfold substInv_k substInv; rw [Poly.substInv_k_eq]; rfl

noncomputable def PolyQ.reduce_k (q : PolyQ) : PolyQ :=
  Bool.rec
    (Bool.rec q ⟨q.num.divConst_k (Int.ofNat (Nat.gcd q.num.gcdCoeffs_k q.den)), Nat.div q.den (Nat.gcd q.num.gcdCoeffs_k q.den)⟩
      (((q.num.divConst_k (Int.ofNat (Nat.gcd q.num.gcdCoeffs_k q.den))).mulConst_k (Int.ofNat (Nat.gcd q.num.gcdCoeffs_k q.den))).beq' q.num
        && Nat.beq (Nat.mul (Nat.div q.den (Nat.gcd q.num.gcdCoeffs_k q.den)) (Nat.gcd q.num.gcdCoeffs_k q.den)) q.den))
    q (Nat.ble (Nat.gcd q.num.gcdCoeffs_k q.den) 1)

theorem PolyQ.reduce_k_eq (q : PolyQ) : q.reduce_k = q.reduce := by
  unfold reduce_k reduce
  rw [Poly.gcdCoeffs_k_eq, Poly.divConst_k_eq, Poly.mulConst_k_eq_mulConst]
  generalize Nat.gcd q.num.gcdCoeffs q.den = g
  dsimp only
  have e₁ : Nat.ble g 1 = decide (g ≤ 1) := by
    cases h : Nat.ble g 1
    · have : ¬ g ≤ 1 := by rw [← Nat.ble_eq, h]; simp
      simp [this]
    · have : g ≤ 1 := by rw [← Nat.ble_eq, h]
      simp [this]
  have e₂ : ((q.num.divConst (Int.ofNat g)).mulConst (Int.ofNat g)).beq' q.num =
      ((q.num.divConst (Int.ofNat g)).mulConst (Int.ofNat g) == q.num) := by
    apply Bool.eq_iff_iff.mpr; rw [Poly.beq'_eq, beq_iff_eq]
  have e₃ : Nat.beq (Nat.mul (Nat.div q.den g) g) q.den = (q.den / g * g == q.den) := rfl
  rw [e₁, e₂, e₃]
  cases decide (g ≤ 1) <;> cases ((q.num.divConst (Int.ofNat g)).mulConst (Int.ofNat g) == q.num && q.den / g * g == q.den) <;> rfl

noncomputable def Poly.toPolyQ_k (p : Poly) (invs : InvVars) (ainvs : InvAtoms) : PolyQ :=
  (invs.foldl (fun (q : PolyQ) xc => q.substInv_k xc.1 xc.2) ⟨p.cancelInvs_k ainvs, 1⟩).reduce_k

@[simp] theorem Poly.toPolyQ_k_eq_toPolyQ (p : Poly) (invs : InvVars) (ainvs : InvAtoms) :
    p.toPolyQ_k invs ainvs = p.toPolyQ invs ainvs := by
  simp only [toPolyQ_k, toPolyQ, cancelInvs_k_eq_cancelInvs, PolyQ.reduce_k_eq, PolyQ.substInv_k_eq]

protected noncomputable def PolyQ.beq' (p q : PolyQ) : Bool :=
  Bool.rec false (Nat.beq p.den q.den) (p.num.beq' q.num)

@[simp] theorem PolyQ.beq'_eq (p q : PolyQ) : p.beq' q = (p = q) := by
  change (p.num.beq' q.num && Nat.beq p.den q.den) = (p = q)
  cases p; cases q; simp

def Expr.toPolyQ (e : Expr) (invs : InvVars) (ainvs : InvAtoms) : PolyQ :=
  e.toPoly.toPolyQ invs ainvs

theorem Poly.denote_substInv [Field α] [IsCharP α 0] (ctx : Context α) (p : Poly) (x : Var) (c : Nat)
    (h : x.denote ctx = (OfNat.ofNat (α := α) c)⁻¹) : (p.substInv x c).denote ctx = p.denote ctx := by
  simp only [substInv, PolyQ.denote, cond_eq_ite]
  split
  next hc =>
    simp at hc; subst hc
    simp [Semiring.natCast_one, Field.inv_one, Semiring.mul_one]
  next hc =>
    simp at hc
    have hc' : (c : α) ≠ 0 := Field.natCast_ne_zero hc
    have h1 : ((c : Int) : α) * x.denote ctx = 1 := by
      rw [Ring.intCast_natCast, h, ← Semiring.ofNat_eq_natCast, Field.mul_inv_cancel]
      rw [Semiring.ofNat_eq_natCast]; exact hc'
    have hpow : (c : α) ^ p.maxDegreeOf x ≠ 0 := fun h => hc' (Field.of_pow_eq_zero _ _ h)
    simp only
    rw [Poly.denote_cancelVar ctx _ (c : Int) x (by omega) h1, Poly.denote_mulConst, Ring.intCast_natCast,
      Semiring.natCast_pow, CommSemiring.mul_comm _ (p.denote ctx), Semiring.mul_assoc,
      Field.mul_inv_cancel hpow, Semiring.mul_one]

theorem PolyQ.denote_substInv [Field α] [IsCharP α 0] (ctx : Context α) (q : PolyQ) (x : Var) (c : Nat)
    (h : x.denote ctx = (OfNat.ofNat (α := α) c)⁻¹) : (q.substInv x c).denote ctx = q.denote ctx := by
  have := Poly.denote_substInv ctx q.num x c h
  simp only [PolyQ.substInv, PolyQ.denote] at this ⊢
  rw [Semiring.natCast_mul, Field.inv_mul, ← this, Semiring.mul_assoc, CommSemiring.mul_comm ((q.den : α)⁻¹)]

private theorem mul_inv_cancel_aux [Field α] {g a b : α} (hg : g ≠ 0) : g * a * (b⁻¹ * g⁻¹) = a * b⁻¹ := by
  rw [CommSemiring.mul_comm b⁻¹, ← Semiring.mul_assoc, Semiring.mul_assoc g a, CommSemiring.mul_comm a,
    ← Semiring.mul_assoc, Field.mul_inv_cancel hg, Semiring.one_mul]

theorem PolyQ.denote_reduce [Field α] [IsCharP α 0] (ctx : Context α) (q : PolyQ) :
    q.reduce.denote ctx = q.denote ctx := by
  unfold reduce
  simp only [cond_eq_ite]
  split
  next => rfl
  next hg =>
    split
    next h =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      simp only [decide_eq_true_eq, Nat.not_le] at hg
      obtain ⟨h₁, h₂⟩ := h
      generalize Nat.gcd q.num.gcdCoeffs q.den = g at *
      generalize q.num.divConst g = num at *
      generalize q.den / g = den at *
      have hg' : (g : α) ≠ 0 := Field.natCast_ne_zero (by omega)
      simp only [PolyQ.denote]
      rw [← h₁, ← h₂, Poly.denote_mulConst, Ring.intCast_natCast, Semiring.natCast_mul, Field.inv_mul,
        mul_inv_cancel_aux hg']
    next => rfl

theorem Poly.denote_toPolyQ [Field α] [IsCharP α 0] (ctx : Context α) (p : Poly) (invs : InvVars)
    (ainvs : InvAtoms) (h : invs.ok ctx) (h' : ainvs.ok ctx) : (p.toPolyQ invs ainvs).denote ctx = p.denote ctx := by
  unfold toPolyQ; rw [PolyQ.denote_reduce]
  suffices ∀ q : PolyQ, (invs.foldl (fun q xc => q.substInv xc.1 xc.2) q).denote ctx = q.denote ctx by
    rw [this]; simp [PolyQ.denote, Semiring.natCast_one, Field.inv_one, Semiring.mul_one, Poly.denote_cancelInvs _ _ _ h']
  induction invs with
  | nil => intro q; rfl
  | cons xc invs ih =>
    intro q
    rw [InvVars.ok_cons] at h
    rw [List.foldl_cons, ih h.2, PolyQ.denote_substInv _ _ _ _ h.1]

theorem Expr.denote_toPolyQ [Field α] [IsCharP α 0] (ctx : Context α) (e : Expr) (invs : InvVars)
    (ainvs : InvAtoms) (h : invs.ok ctx) (h' : ainvs.ok ctx) : (e.toPolyQ invs ainvs).denote ctx = e.denote ctx := by
  rw [toPolyQ, Poly.denote_toPolyQ _ _ _ _ h h', Expr.denote_toPoly]

theorem Poly.substInv_den_ne_zero (p : Poly) (x : Var) (c : Nat) : (p.substInv x c).den ≠ 0 := by
  simp only [substInv, cond_eq_ite]
  split
  next => simp
  next h => simp at h; intro h'; exact h (Nat.pow_eq_zero.mp h').1

theorem PolyQ.reduce_den_ne_zero (q : PolyQ) (h : q.den ≠ 0) : q.reduce.den ≠ 0 := by
  unfold reduce
  simp only [cond_eq_ite]
  split
  next => exact h
  next =>
    split
    next h' =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h'
      intro hd
      have h₂ := h'.2
      simp only at hd
      rw [hd, Nat.zero_mul] at h₂
      exact h h₂.symm
    next => exact h

theorem Poly.toPolyQ_den_ne_zero (p : Poly) (invs : InvVars) (ainvs : InvAtoms) : (p.toPolyQ invs ainvs).den ≠ 0 := by
  unfold toPolyQ; apply PolyQ.reduce_den_ne_zero
  suffices ∀ q : PolyQ, q.den ≠ 0 → (invs.foldl (fun q xc => q.substInv xc.1 xc.2) q).den ≠ 0 from
    this ⟨p.cancelInvs ainvs, 1⟩ Nat.one_ne_zero
  induction invs with
  | nil => intro q h; exact h
  | cons xc invs ih =>
    intro q h
    rw [List.foldl_cons]
    apply ih
    exact Nat.mul_ne_zero h (Poly.substInv_den_ne_zero q.num xc.1 xc.2)

theorem Expr.toPolyQ_den_ne_zero (e : Expr) (invs : InvVars) (ainvs : InvAtoms) : (e.toPolyQ invs ainvs).den ≠ 0 :=
  Poly.toPolyQ_den_ne_zero e.toPoly invs ainvs

/-!
Balanced elimination of numeral inverses. `Poly.cancelVar_k` inserts each monomial into the
result, and cancelling `x` changes the order of the monomials, so the kernel performs a quadratic
number of comparisons; `Poly.cancelVarB_k` adds the cancelled monomials pairwise instead.
-/

/-- The monomials of `p` with `x` cancelled, as `Poly.cancelVar` does, each as a polynomial. -/
noncomputable def Poly.cancelTerms_k (c : Int) (x : Var) (p : Poly) : List Poly :=
  Poly.rec (fun k => [.num k])
    (fun k m _ ih =>
      Bool.rec (.add k m (.num 0))
        (.add (Int.ediv_k k (Int.pow_k c (Mon.degreeOf_k m x))) (Mon.cancelVar_k m x) (.num 0))
        (Nat.blt 0 (Mon.degreeOf_k m x) && Int.beqZero_k (Int.emod_k k (Int.pow_k c (Mon.degreeOf_k m x)))) :: ih)
    p

noncomputable def Poly.cancelVarB_k (c : Int) (x : Var) (p : Poly) : Poly :=
  sumB_k combine_k (p.cancelTerms_k c x)

noncomputable def Poly.substInvB_k (p : Poly) (x : Var) (c : Nat) : PolyQ :=
  Bool.rec
    ⟨(p.mulConst_k (Int.ofNat (Nat.pow c (p.maxDegreeOf_k x)))).cancelVarB_k (Int.ofNat c) x, Nat.pow c (p.maxDegreeOf_k x)⟩
    ⟨p, 1⟩ (Nat.beq c 0)

noncomputable def PolyQ.substInvB_k (q : PolyQ) (x : Var) (c : Nat) : PolyQ :=
  ⟨(q.num.substInvB_k x c).num, Nat.mul q.den (q.num.substInvB_k x c).den⟩

/-- `Poly.toPolyQ_k` with `Poly.cancelVarB_k` if `bal`. -/
noncomputable def Poly.toPolyQX_k (bal : Bool) (p : Poly) (invs : InvVars) (ainvs : InvAtoms) : PolyQ :=
  Bool.rec (p.toPolyQ_k invs ainvs)
    ((invs.foldl (fun (q : PolyQ) xc => q.substInvB_k xc.1 xc.2) ⟨p.cancelInvs_k ainvs, 1⟩).reduce_k) bal

theorem Poly.denoteList_cancelTerms_k {α} [CommRing α] (ctx : Context α) (p : Poly) (c : Int) (x : Var)
    (h₁ : c ≠ 0) (h₂ : c * x.denote ctx = 1) : denoteList ctx (p.cancelTerms_k c x) = p.denote ctx := by
  induction p with
  | num k => show ((k : Int) : α) + 0 = _; rw [Semiring.add_zero]; rfl
  | add k m p ih =>
    show Poly.denote ctx (Bool.rec _ _ _) + denoteList ctx (p.cancelTerms_k c x) = _
    rw [ih, Mon.degreeOf_k_eq_degreeOf, Mon.cancelVar_k_eq_cancelVar, Int.pow_k_eq, Int.emod_k_eq, Int.ediv_k_eq,
      Int.beqZero_k_eq]
    cases h : (Nat.blt 0 (m.degreeOf x) && (k % c ^ m.degreeOf x == 0))
    · show k • m.denote ctx + ((0 : Int) : α) + _ = _
      rw [Ring.intCast_zero, Semiring.add_zero]; rfl
    · show (k / c ^ m.degreeOf x) • (m.cancelVar x).denote ctx + ((0 : Int) : α) + _ = _
      rw [Ring.intCast_zero, Semiring.add_zero]
      show _ = k • m.denote ctx + p.denote ctx
      congr 1
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have ⟨d, hd⟩ : c ^ m.degreeOf x ∣ k := Int.dvd_of_emod_eq_zero h.2
      rw [Ring.zsmul_eq_intCast_mul, Ring.zsmul_eq_intCast_mul, Mon.denote_cancelVar ctx m x, hd,
        Int.mul_ediv_cancel_left _ (Int.pow_ne_zero h₁), Ring.intCast_mul, Ring.intCast_pow]
      rw [CommSemiring.mul_comm ((c : α) ^ _), Semiring.mul_assoc, ← Semiring.mul_assoc ((c : α) ^ _),
        ← CommSemiring.mul_pow, h₂, Semiring.one_pow, Semiring.one_mul]

theorem Poly.denote_cancelVarB_k {α} [CommRing α] (ctx : Context α) (p : Poly) (c : Int) (x : Var)
    (h₁ : c ≠ 0) (h₂ : c * x.denote ctx = 1) : (p.cancelVarB_k c x).denote ctx = p.denote ctx := by
  rw [cancelVarB_k, denote_sumB_k ctx _ (denote_combine_k ctx), denoteList_cancelTerms_k ctx p c x h₁ h₂]

theorem Poly.substInvB_k_den (p : Poly) (x : Var) (c : Nat) : (p.substInvB_k x c).den = (p.substInv x c).den := by
  unfold substInvB_k substInv
  cases h : Nat.beq c 0
  · have : (c == 0) = false := h
    simp only [this, Bool.cond_false]; rw [Poly.maxDegreeOf_k_eq]; rfl
  · have : (c == 0) = true := h
    simp only [this, Bool.cond_true]

theorem Poly.denote_substInvB_k [Field α] [IsCharP α 0] (ctx : Context α) (p : Poly) (x : Var) (c : Nat)
    (h : x.denote ctx = (OfNat.ofNat (α := α) c)⁻¹) : (p.substInvB_k x c).denote ctx = p.denote ctx := by
  unfold substInvB_k
  cases hb : Nat.beq c 0
  · have hc : c ≠ 0 := Nat.ne_of_beq_eq_false hb
    have hc' : (c : α) ≠ 0 := Field.natCast_ne_zero hc
    have h1 : ((c : Int) : α) * x.denote ctx = 1 := by
      rw [Ring.intCast_natCast, h, ← Semiring.ofNat_eq_natCast, Field.mul_inv_cancel]
      rw [Semiring.ofNat_eq_natCast]; exact hc'
    have hpow : (c : α) ^ p.maxDegreeOf x ≠ 0 := fun h => hc' (Field.of_pow_eq_zero _ _ h)
    show ((p.mulConst_k (Int.ofNat (Nat.pow c (p.maxDegreeOf_k x)))).cancelVarB_k (Int.ofNat c) x).denote ctx
      * ((Nat.pow c (p.maxDegreeOf_k x) : Nat) : α)⁻¹ = _
    rw [Int.ofNat_eq_natCast, Poly.denote_cancelVarB_k ctx _ (c : Int) x (by omega) h1, Poly.maxDegreeOf_k_eq, Poly.mulConst_k_eq_mulConst,
      Poly.denote_mulConst, Int.ofNat_eq_natCast, Ring.intCast_natCast, Nat.pow_eq,
      Semiring.natCast_pow, CommSemiring.mul_comm _ (p.denote ctx), Semiring.mul_assoc,
      Field.mul_inv_cancel hpow, Semiring.mul_one]
  · show p.denote ctx * ((1 : Nat) : α)⁻¹ = _
    rw [Semiring.natCast_one, Field.inv_one, Semiring.mul_one]

theorem PolyQ.denote_substInvB_k [Field α] [IsCharP α 0] (ctx : Context α) (q : PolyQ) (x : Var) (c : Nat)
    (h : x.denote ctx = (OfNat.ofNat (α := α) c)⁻¹) : (q.substInvB_k x c).denote ctx = q.denote ctx := by
  have := Poly.denote_substInvB_k ctx q.num x c h
  simp only [PolyQ.substInvB_k, PolyQ.denote] at this ⊢
  rw [Nat.mul_eq, Semiring.natCast_mul, Field.inv_mul, ← this, Semiring.mul_assoc, CommSemiring.mul_comm ((q.den : α)⁻¹)]

theorem Poly.denote_toPolyQX_k [Field α] [IsCharP α 0] (ctx : Context α) (bal : Bool) (p : Poly) (invs : InvVars)
    (ainvs : InvAtoms) (h : invs.ok ctx) (h' : ainvs.ok ctx) : (p.toPolyQX_k bal invs ainvs).denote ctx = p.denote ctx := by
  cases bal
  · show (p.toPolyQ_k invs ainvs).denote ctx = _; rw [toPolyQ_k_eq_toPolyQ, denote_toPolyQ ctx p invs ainvs h h']
  · show (PolyQ.reduce_k _).denote ctx = _
    rw [PolyQ.reduce_k_eq, PolyQ.denote_reduce]
    suffices ∀ q : PolyQ, (invs.foldl (fun q xc => q.substInvB_k xc.1 xc.2) q).denote ctx = q.denote ctx by
      rw [this]; simp [PolyQ.denote, Semiring.natCast_one, Field.inv_one, Semiring.mul_one, cancelInvs_k_eq_cancelInvs,
        Poly.denote_cancelInvs _ _ _ h']
    induction invs with
    | nil => intro q; rfl
    | cons xc invs ih =>
      intro q
      rw [InvVars.ok_cons] at h
      rw [List.foldl_cons, ih h.2, PolyQ.denote_substInvB_k _ _ _ _ h.1]

theorem Poly.toPolyQX_k_den_ne_zero (bal : Bool) (p : Poly) (invs : InvVars) (ainvs : InvAtoms) :
    (p.toPolyQX_k bal invs ainvs).den ≠ 0 := by
  cases bal
  · show (p.toPolyQ_k invs ainvs).den ≠ 0; rw [toPolyQ_k_eq_toPolyQ]; exact toPolyQ_den_ne_zero p invs ainvs
  · show (PolyQ.reduce_k _).den ≠ 0
    rw [PolyQ.reduce_k_eq]; apply PolyQ.reduce_den_ne_zero
    suffices ∀ q : PolyQ, q.den ≠ 0 → (invs.foldl (fun q xc => q.substInvB_k xc.1 xc.2) q).den ≠ 0 from
      this _ Nat.one_ne_zero
    induction invs with
    | nil => intro q h; exact h
    | cons xc invs ih =>
      intro q h
      rw [List.foldl_cons]
      apply ih
      show Nat.mul q.den (q.num.substInvB_k xc.1 xc.2).den ≠ 0
      rw [Poly.substInvB_k_den]
      exact Nat.mul_ne_zero h (Poly.substInv_den_ne_zero q.num xc.1 xc.2)

private theorem sub_nonpos_iff [Ring α] [LE α] [IsPreorder α] [OrderedAdd α] {a b : α} : a - b ≤ 0 ↔ a ≤ b := by
  rw [← OrderedAdd.neg_nonneg_iff, AddCommGroup.neg_sub, OrderedAdd.sub_nonneg_iff]

private theorem sub_neg_iff [Ring α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a b : α} :
    a - b < 0 ↔ a < b := by
  rw [← OrderedAdd.neg_pos_iff, AddCommGroup.neg_sub, OrderedAdd.sub_pos_iff]

/-! ## Certificates for inverses of atoms only -/

noncomputable def Expr.cancelInvs_cert (ainvs : InvAtoms) (a b : Expr) : Bool :=
  (a.toPoly_k.cancelInvs_k ainvs).beq' (b.toPoly_k.cancelInvs_k ainvs)

theorem Expr.eq_of_cancelInvs_eq [CommRing α] (ctx : Context α) (ainvs : InvAtoms) (hok : ainvs.ok ctx)
    (a b : Expr) (h : cancelInvs_cert ainvs a b) : a.denote ctx = b.denote ctx := by
  simp only [cancelInvs_cert, Poly.beq'_eq, Poly.cancelInvs_k_eq_cancelInvs, Expr.toPoly_k_eq_toPoly] at h
  have := congrArg (Poly.denote ctx) h
  rwa [Poly.denote_cancelInvs _ _ _ hok, Poly.denote_cancelInvs _ _ _ hok, Expr.denote_toPoly, Expr.denote_toPoly] at this

noncomputable def normA_cert (ainvs : InvAtoms) (lhs rhs lhs' rhs' : Expr) : Bool :=
  ((lhs.sub rhs).toPoly_k.cancelInvs_k ainvs).beq' (lhs'.sub rhs').toPoly_k

private theorem denote_sub_of_normA_cert [CommRing α] (ctx : Context α) (ainvs : InvAtoms) (hok : ainvs.ok ctx)
    (lhs rhs lhs' rhs' : Expr) (h : normA_cert ainvs lhs rhs lhs' rhs') :
    lhs.denote ctx - rhs.denote ctx = lhs'.denote ctx - rhs'.denote ctx := by
  simp only [normA_cert, Poly.beq'_eq, Poly.cancelInvs_k_eq_cancelInvs, Expr.toPoly_k_eq_toPoly] at h
  have := congrArg (Poly.denote ctx) h
  rw [Poly.denote_cancelInvs _ _ _ hok, Expr.denote_toPoly, Expr.denote_toPoly] at this
  exact this

theorem eq_normA_expr [CommRing α] (ctx : Context α) (ainvs : InvAtoms) (hok : ainvs.ok ctx) (lhs rhs lhs' rhs' : Expr) :
    normA_cert ainvs lhs rhs lhs' rhs' → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  intro h
  have h := denote_sub_of_normA_cert ctx ainvs hok lhs rhs lhs' rhs' h
  rw [← AddCommGroup.sub_eq_zero_iff (a := lhs.denote ctx) (b := rhs.denote ctx),
    ← AddCommGroup.sub_eq_zero_iff (a := lhs'.denote ctx) (b := rhs'.denote ctx), h]

theorem le_normA_expr [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (ainvs : InvAtoms)
    (hok : ainvs.ok ctx) (lhs rhs lhs' rhs' : Expr) :
    normA_cert ainvs lhs rhs lhs' rhs' → (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  intro h
  have h := denote_sub_of_normA_cert ctx ainvs hok lhs rhs lhs' rhs' h
  rw [← sub_nonpos_iff, ← sub_nonpos_iff (a := lhs'.denote ctx), h]

theorem lt_normA_expr [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α)
    (ainvs : InvAtoms) (hok : ainvs.ok ctx) (lhs rhs lhs' rhs' : Expr) :
    normA_cert ainvs lhs rhs lhs' rhs' → (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  intro h
  have h := denote_sub_of_normA_cert ctx ainvs hok lhs rhs lhs' rhs' h
  rw [← sub_neg_iff, ← sub_neg_iff (a := lhs'.denote ctx), h]

/-! ## Certificates for rational coefficients -/

noncomputable def Expr.toPolyQ_cert (bal : Bool) (invs : InvVars) (ainvs : InvAtoms) (a b : Expr) : Bool :=
  ((a.toPolyX_k bal).toPolyQX_k bal invs ainvs).beq' ((b.toPolyX_k bal).toPolyQX_k bal invs ainvs)

theorem Expr.eq_of_toPolyQ_eq [Field α] [IsCharP α 0] (ctx : Context α) (bal : Bool) (invs : InvVars) (hok : invs.ok ctx)
    (ainvs : InvAtoms) (hoka : ainvs.ok ctx) (a b : Expr) (h : toPolyQ_cert bal invs ainvs a b) :
    a.denote ctx = b.denote ctx := by
  simp only [toPolyQ_cert, PolyQ.beq'_eq] at h
  have ha := Poly.denote_toPolyQX_k ctx bal (a.toPolyX_k bal) invs ainvs hok hoka
  have hb := Poly.denote_toPolyQX_k ctx bal (b.toPolyX_k bal) invs ainvs hok hoka
  rw [Expr.denote_toPolyX_k] at ha hb
  rw [← ha, ← hb, h]

/-- `lhs' - rhs'` is the numerator of `lhs - rhs`; the relation between `lhs'` and `rhs'` is denominator-free. -/
noncomputable def normQ_cert (bal : Bool) (invs : InvVars) (ainvs : InvAtoms) (lhs rhs lhs' rhs' : Expr) : Bool :=
  (((lhs.sub rhs).toPolyX_k bal).toPolyQX_k bal invs ainvs).num.beq' ((lhs'.sub rhs').toPolyX_k bal)

private theorem denote_sub_of_normQ_cert [Field α] [IsCharP α 0] (ctx : Context α) (bal : Bool) (invs : InvVars) (hok : invs.ok ctx)
    (ainvs : InvAtoms) (hoka : ainvs.ok ctx) (lhs rhs lhs' rhs' : Expr) (h : normQ_cert bal invs ainvs lhs rhs lhs' rhs') :
    ∃ d : Nat, d ≠ 0 ∧ lhs.denote ctx - rhs.denote ctx = (lhs'.denote ctx - rhs'.denote ctx) * (d : α)⁻¹ := by
  simp only [normQ_cert, Poly.beq'_eq] at h
  refine ⟨(((lhs.sub rhs).toPolyX_k bal).toPolyQX_k bal invs ainvs).den,
    Poly.toPolyQX_k_den_ne_zero bal _ invs ainvs, ?_⟩
  have h₁ := Poly.denote_toPolyQX_k ctx bal ((lhs.sub rhs).toPolyX_k bal) invs ainvs hok hoka
  have h₂ := Expr.denote_toPolyX_k ctx bal (lhs'.sub rhs')
  rw [Expr.denote_toPolyX_k] at h₁
  simp only [PolyQ.denote, h] at h₁
  replace h₁ : ((lhs'.sub rhs').toPolyX_k bal).denote ctx * ((((lhs.sub rhs).toPolyX_k bal).toPolyQX_k bal invs ainvs).den : α)⁻¹
      = lhs.denote ctx - rhs.denote ctx := h₁
  replace h₂ : ((lhs'.sub rhs').toPolyX_k bal).denote ctx = lhs'.denote ctx - rhs'.denote ctx := h₂
  rw [← h₁, h₂]

theorem eq_normQ_expr [Field α] [IsCharP α 0] (ctx : Context α) (bal : Bool) (invs : InvVars) (hok : invs.ok ctx)
    (ainvs : InvAtoms) (hoka : ainvs.ok ctx) (lhs rhs lhs' rhs' : Expr) :
    normQ_cert bal invs ainvs lhs rhs lhs' rhs' → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  intro h
  obtain ⟨d, hd, h⟩ := denote_sub_of_normQ_cert ctx bal invs hok ainvs hoka lhs rhs lhs' rhs' h
  have hd' : (d : α)⁻¹ ≠ 0 := by rw [Ne, Field.inv_eq_zero_iff]; exact Field.natCast_ne_zero hd
  rw [← AddCommGroup.sub_eq_zero_iff (a := lhs.denote ctx) (b := rhs.denote ctx),
    ← AddCommGroup.sub_eq_zero_iff (a := lhs'.denote ctx) (b := rhs'.denote ctx), h]
  apply propext; constructor
  · intro h0
    rcases Field.of_mul_eq_zero h0 with h0 | h0
    · exact h0
    · exact absurd h0 hd'
  · intro h0; rw [h0, Semiring.zero_mul]

theorem eq_true_of_polyQ0 [Field α] [IsCharP α 0] (ctx : Context α) (bal : Bool) (invs : InvVars) (hok : invs.ok ctx)
    (ainvs : InvAtoms) (hoka : ainvs.ok ctx) (lhs rhs : Expr)
    (h : (((lhs.sub rhs).toPolyX_k bal).toPolyQX_k bal invs ainvs).num = .num 0) :
    (lhs.denote ctx = rhs.denote ctx) = True := by
  have h₁ := Poly.denote_toPolyQX_k ctx bal ((lhs.sub rhs).toPolyX_k bal) invs ainvs hok hoka
  rw [Expr.denote_toPolyX_k] at h₁
  simp only [PolyQ.denote, h] at h₁
  replace h₁ : ((0 : Int) : α) * (((((lhs.sub rhs).toPolyX_k bal).toPolyQX_k bal invs ainvs).den : Nat) : α)⁻¹
      = lhs.denote ctx - rhs.denote ctx := h₁
  rw [Ring.intCast_zero, Semiring.zero_mul] at h₁
  exact eq_true (AddCommGroup.sub_eq_zero_iff.mp h₁.symm)

theorem eq_true_of_toPolyQ_eq [Field α] [IsCharP α 0] (ctx : Context α) (bal₁ bal₂ : Bool) (invs : InvVars)
    (hok : invs.ok ctx) (ainvs : InvAtoms) (hoka : ainvs.ok ctx) (lhs rhs : Expr) (q : PolyQ)
    (h₁ : q = (lhs.toPolyX_k bal₁).toPolyQX_k bal₁ invs ainvs) (h₂ : q = (rhs.toPolyX_k bal₂).toPolyQX_k bal₂ invs ainvs) :
    (lhs.denote ctx = rhs.denote ctx) = True := by
  have e₁ := Poly.denote_toPolyQX_k ctx bal₁ (lhs.toPolyX_k bal₁) invs ainvs hok hoka
  have e₂ := Poly.denote_toPolyQX_k ctx bal₂ (rhs.toPolyX_k bal₂) invs ainvs hok hoka
  rw [← h₁, Expr.denote_toPolyX_k] at e₁
  rw [← h₂, Expr.denote_toPolyX_k] at e₂
  exact eq_true (e₁.symm.trans e₂)

section
variable {α : Type u} [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]

private theorem mul_inv_nonpos_iff {a d : α} (hd : 0 < d) : a * d⁻¹ ≤ 0 ↔ a ≤ 0 := by
  have := Field.IsOrdered.mul_le_mul_iff_of_pos_right (a := a) (b := 0) (Field.IsOrdered.inv_pos_iff.mpr hd)
  rwa [Semiring.zero_mul] at this

private theorem mul_inv_neg_iff {a d : α} (hd : 0 < d) : a * d⁻¹ < 0 ↔ a < 0 := by
  have := Field.IsOrdered.mul_lt_mul_iff_of_pos_right (a := a) (b := 0) (Field.IsOrdered.inv_pos_iff.mpr hd)
  rwa [Semiring.zero_mul] at this

end

section
variable {α : Type u} [Field α] [IsCharP α 0] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]

theorem le_normQ_expr (ctx : Context α) (bal : Bool) (invs : InvVars) (hok : invs.ok ctx) (ainvs : InvAtoms) (hoka : ainvs.ok ctx)
    (lhs rhs lhs' rhs' : Expr) :
    normQ_cert bal invs ainvs lhs rhs lhs' rhs' → (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  intro h
  obtain ⟨d, hd, h⟩ := denote_sub_of_normQ_cert ctx bal invs hok ainvs hoka lhs rhs lhs' rhs' h
  have hd' : (0 : α) < d := OrderedRing.pos_natCast_of_pos d (Nat.pos_of_ne_zero hd)
  rw [← sub_nonpos_iff, ← sub_nonpos_iff (a := lhs'.denote ctx), h, mul_inv_nonpos_iff hd']

theorem lt_normQ_expr (ctx : Context α) (bal : Bool) (invs : InvVars) (hok : invs.ok ctx) (ainvs : InvAtoms) (hoka : ainvs.ok ctx)
    (lhs rhs lhs' rhs' : Expr) :
    normQ_cert bal invs ainvs lhs rhs lhs' rhs' → (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  intro h
  obtain ⟨d, hd, h⟩ := denote_sub_of_normQ_cert ctx bal invs hok ainvs hoka lhs rhs lhs' rhs' h
  have hd' : (0 : α) < d := OrderedRing.pos_natCast_of_pos d (Nat.pos_of_ne_zero hd)
  rw [← sub_neg_iff, ← sub_neg_iff (a := lhs'.denote ctx), h, mul_inv_neg_iff hd']

end

end Lean.Grind.CommRing
