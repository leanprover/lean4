/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Lemmas
import Init.Data.Hashable
import Init.Data.Ord
import Init.Data.RArray
import Init.Grind.CommRing.Basic

namespace Lean.Grind
namespace CommRing

abbrev Var := Nat

inductive Expr where
  | num  (v : Int)
  | var  (i : Var)
  | neg (a : Expr)
  | add  (a b : Expr)
  | sub  (a b : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (k : Nat)
  deriving Inhabited, BEq

abbrev Context (α : Type u) := RArray α

def Var.denote {α} (ctx : Context α) (v : Var) : α :=
  ctx.get v

def denoteInt {α} [CommRing α] (k : Int) : α :=
  bif k < 0 then
    - OfNat.ofNat (α := α) k.natAbs
  else
    OfNat.ofNat (α := α) k.natAbs

def Expr.denote {α} [CommRing α] (ctx : Context α) : Expr → α
  | .add a b  => denote ctx a + denote ctx b
  | .sub a b  => denote ctx a - denote ctx b
  | .mul a b  => denote ctx a * denote ctx b
  | .neg a    => -denote ctx a
  | .num k    => denoteInt k
  | .var v    => v.denote ctx
  | .pow a k  => denote ctx a ^ k

structure Power where
  x : Var
  k : Nat
  deriving BEq, Repr, Inhabited

instance : LawfulBEq Power where
  eq_of_beq {a} := by cases a <;> intro b <;> cases b <;> simp_all! [BEq.beq]
  rfl := by intro a; cases a <;> simp! [BEq.beq]

def Power.varLt (p₁ p₂ : Power) : Bool :=
  p₁.x.blt p₂.x

def Power.denote {α} [CommRing α] (ctx : Context α) : Power → α
  | {x, k} =>
    match k with
    | 0 => 1
    | 1 => x.denote ctx
    | k => x.denote ctx ^ k

inductive Mon where
  | unit
  | mult (p : Power) (m : Mon)
  deriving BEq, Repr, Inhabited

instance : LawfulBEq Mon where
  eq_of_beq {a} := by
    induction a <;> intro b <;> cases b <;> simp_all! [BEq.beq]
    next p₁ m₁ p₂ m₂ ih =>
      cases p₁ <;> cases p₂ <;> simp <;> intros <;> simp [*]
      next h => exact ih h
  rfl := by
    intro a
    induction a <;> simp! [BEq.beq]
    assumption

def Mon.denote {α} [CommRing α] (ctx : Context α) : Mon → α
  | unit => 1
  | .mult p m => p.denote ctx * denote ctx m

def Mon.ofVar (x : Var) : Mon :=
  .mult { x, k := 1 } .unit

def Mon.concat (m₁ m₂ : Mon) : Mon :=
  match m₁ with
  | .unit => m₂
  | .mult pw m₁ => .mult pw (concat m₁ m₂)

def Mon.mulPow (pw : Power) (m : Mon) : Mon :=
  match m with
  | .unit =>
    .mult pw .unit
  | .mult pw' m =>
    bif pw.varLt pw' then
      .mult pw (.mult pw' m)
    else bif pw'.varLt pw then
      .mult pw' (mulPow pw m)
    else
      .mult { x := pw.x, k := pw.k + pw'.k } m

def Mon.length : Mon → Nat
  | .unit => 0
  | .mult _ m => 1 + length m

def hugeFuel := 1000000

def Mon.mul (m₁ m₂ : Mon) : Mon :=
  -- We could use `m₁.length + m₂.length` to avoid hugeFuel
  go hugeFuel m₁ m₂
where
  go (fuel : Nat) (m₁ m₂ : Mon) : Mon :=
    match fuel with
    | 0 => concat m₁ m₂
    | fuel + 1 =>
      match m₁, m₂ with
      | m₁, .unit => m₁
      | .unit, m₂ => m₂
      | .mult pw₁ m₁, .mult pw₂ m₂ =>
        bif pw₁.varLt pw₂ then
          .mult pw₁ (go fuel m₁ (.mult pw₂ m₂))
        else bif pw₂.varLt pw₁ then
          .mult pw₂ (go fuel (.mult pw₁ m₁) m₂)
        else
          .mult { x := pw₁.x, k := pw₁.k + pw₂.k } (go fuel m₁ m₂)

def Mon.degree : Mon → Nat
  | .unit => 0
  | .mult pw m => pw.k + degree m

def Var.revlex (x y : Var) : Ordering :=
  bif x.blt y then .gt
  else bif y.blt x then .lt
  else .eq

def powerRevlex (k₁ k₂ : Nat) : Ordering :=
  bif k₁.blt k₂ then .gt
  else bif k₂.blt k₁ then .lt
  else .eq

def Power.revlex (p₁ p₂ : Power) : Ordering :=
  p₁.x.revlex p₂.x |>.then (powerRevlex p₁.k p₂.k)

def Mon.revlexWF (m₁ m₂ : Mon) : Ordering :=
  match m₁, m₂ with
  | .unit, .unit => .eq
  | .unit, .mult .. => .gt
  | .mult .., .unit => .lt
  | .mult pw₁ m₁, .mult pw₂ m₂ =>
    bif pw₁.x == pw₂.x then
      revlexWF m₁ m₂ |>.then (powerRevlex pw₁.k pw₂.k)
    else bif pw₁.x.blt pw₂.x then
      revlexWF m₁ (.mult pw₂ m₂) |>.then .gt
    else
      revlexWF (.mult pw₁ m₁) m₂ |>.then .lt

def Mon.revlexFuel (fuel : Nat) (m₁ m₂ : Mon) : Ordering :=
  match fuel with
  | 0 =>
    -- This branch is not reachable in practice, but we add it here
    -- to ensure we can prove helper theorems
    revlexWF m₁ m₂
  | fuel + 1 =>
    match m₁, m₂ with
    | .unit, .unit => .eq
    | .unit, .mult ..  => .gt
    | .mult .., .unit => .lt
    | .mult pw₁ m₁, .mult pw₂ m₂ =>
      bif pw₁.x == pw₂.x then
        revlexFuel fuel m₁ m₂ |>.then (powerRevlex pw₁.k pw₂.k)
      else bif pw₁.x.blt pw₂.x then
        revlexFuel fuel m₁ (.mult pw₂ m₂) |>.then .gt
      else
        revlexFuel fuel (.mult pw₁ m₁) m₂ |>.then .lt

def Mon.revlex (m₁ m₂ : Mon) : Ordering :=
  revlexFuel hugeFuel m₁ m₂

def Mon.grevlex (m₁ m₂ : Mon) : Ordering :=
  compare m₁.degree m₂.degree |>.then (revlex m₁ m₂)

inductive Poly where
  | num (k : Int)
  | add (k : Int) (v : Mon) (p : Poly)
  deriving BEq, Inhabited

instance : LawfulBEq Poly where
  eq_of_beq {a} := by
    induction a <;> intro b <;> cases b <;> simp_all! [BEq.beq]
    intro h₁ h₂ h₃
    next m₁ p₁ _ m₂ p₂ ih =>
    replace h₂ : m₁ == m₂ := h₂
    simp [ih h₃, eq_of_beq h₂]
  rfl := by
    intro a
    induction a <;> simp! [BEq.beq]
    next k m p ih =>
    show m == m ∧ p == p
    simp [ih]

def Poly.denote [CommRing α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => Int.cast k
  | .add k m p => Int.cast k * m.denote ctx + denote ctx p

def Poly.ofMon (m : Mon) : Poly :=
  .add 1 m (.num 0)

def Poly.ofVar (x : Var) : Poly :=
  ofMon (Mon.ofVar x)

def Poly.isSorted : Poly → Bool
  | .num _ => true
  | .add _ _ (.num _) => true
  | .add _ m₁ (.add k m₂ p) => m₁.grevlex m₂ == .gt && (Poly.add k m₂ p).isSorted

def Poly.addConst (p : Poly) (k : Int) : Poly :=
  bif k == 0 then
    p
  else
    go p
where
  go : Poly → Poly
  | .num k' => .num (k' + k)
  | .add k' m p => .add k' m (go p)

def Poly.insert (k : Int) (m : Mon) (p : Poly) : Poly :=
  bif k == 0 then
    p
  else bif m == .unit then
    p.addConst k
  else
    go p
where
  go : Poly → Poly
    | .num k' => .add k m (.num k')
    | .add k' m' p =>
      match m.grevlex m' with
      | .eq =>
        let k := k + k'
        bif k == 0 then
          p
        else
          .add k m p
      | .gt => .add k m (.add k' m' p)
      | .lt => .add k' m' (go p)

def Poly.concat (p₁ p₂ : Poly) : Poly :=
  match p₁ with
  | .num k₁ => p₂.addConst k₁
  | .add k m p₁ => .add k m (concat p₁ p₂)

def Poly.mulConst (k : Int) (p : Poly) : Poly :=
  bif k == 0 then
    .num 0
  else bif k == 1 then
    p
  else
    go p
where
  go : Poly → Poly
   | .num k' => .num (k*k')
   | .add k' m p => .add (k*k') m (go p)

def Poly.mulMon (k : Int) (m : Mon) (p : Poly) : Poly :=
  bif k == 0 then
    .num 0
  else bif m == .unit then
    p.mulConst k
  else
    go p
where
  go : Poly → Poly
   | .num k' =>
     bif k' == 0 then
       .num 0
     else
       .add (k*k') m (.num 0)
   | .add k' m' p => .add (k*k') (m.mul m') (go p)

def Poly.combine (p₁ p₂ : Poly) : Poly :=
  go hugeFuel p₁ p₂
where
  go (fuel : Nat) (p₁ p₂ : Poly) : Poly :=
    match fuel with
    | 0 => p₁.concat p₂
    | fuel + 1 => match p₁, p₂ with
      | .num k₁, .num k₂ => .num (k₁ + k₂)
      | .num k₁, .add k₂ m₂ p₂ => addConst (.add k₂ m₂ p₂) k₁
      | .add k₁ m₁ p₁, .num k₂ => addConst (.add k₁ m₁ p₁) k₂
      | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
        match m₁.grevlex m₂ with
        | .eq =>
          let k := k₁ + k₂
          bif k == 0 then
            go fuel p₁ p₂
          else
            .add k m₁ (go fuel p₁ p₂)
        | .gt => .add k₁ m₁ (go fuel p₁ (.add k₂ m₂ p₂))
        | .lt => .add k₂ m₂ (go fuel (.add k₁ m₁ p₁) p₂)

def Poly.mul (p₁ : Poly) (p₂ : Poly) : Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | .num k => acc.combine (p₂.mulConst k)
    | .add k m p₁ => go p₁ (acc.combine (p₂.mulMon k m))

def Poly.pow (p : Poly) (k : Nat) : Poly :=
  match k with
  | 0 => .num 1
  | 1 => p
  | k+1 => p.mul (pow p k)

def Expr.toPoly : Expr → Poly
  | .num n   => .num n
  | .var x   => Poly.ofVar x
  | .add a b => a.toPoly.combine b.toPoly
  | .mul a b => a.toPoly.mul b.toPoly
  | .neg a   => a.toPoly.mulConst (-1)
  | .sub a b => a.toPoly.combine (b.toPoly.mulConst (-1))
  | .pow a k =>
    match a with
    | .num n => .num (n^k)
    | .var x => Poly.ofMon (.mult {x, k} .unit)
    | _ => a.toPoly.pow k

/-!
**Definitions for the `IsCharP` case**

We considered using a single set of definitions parameterized by `Option c` or simply set `c = 0` since
`n % 0 = n` in Lean, but decided against it to avoid unnecessary kernel‑reduction overhead.
Once we can specialize definitions before they reach the kernel,
we can merge the two versions. Until then, the `IsCharP` definitions will carry the `C` suffix.
We use them whenever we can infer the characteristic using type class instance synthesis.
-/
def Poly.addConstC (p : Poly) (k : Int) (c : Nat) : Poly :=
  match p with
  | .num k' => .num ((k' + k) % c)
  | .add k' m p => .add k' m (addConstC p k c)

def Poly.insertC (k : Int) (m : Mon) (p : Poly) (c : Nat) : Poly :=
  let k := k % c
  bif k == 0 then
    p
  else
    go k p
where
  go (k : Int) : Poly → Poly
    | .num k' => .add k m (.num k')
    | .add k' m' p =>
      match m.grevlex m' with
      | .eq =>
        let k'' := (k + k') % c
        bif k'' == 0 then
          p
        else
          .add k'' m p
      | .gt => .add k m (.add k' m' p)
      | .lt => .add k' m' (go k p)

def Poly.mulConstC (k : Int) (p : Poly) (c : Nat) : Poly :=
  let k := k % c
  bif k == 0 then
    .num 0
  else bif k == 1 then
    p
  else
    go p
where
  go : Poly → Poly
   | .num k' => .num ((k*k') % c)
   | .add k' m p =>
     let k := (k*k') % c
     bif k == 0 then
      go p
    else
      .add k m (go p)

def Poly.mulMonC (k : Int) (m : Mon) (p : Poly) (c : Nat) : Poly :=
  let k := k % c
  bif k == 0 then
    .num 0
  else
    go p
where
  go : Poly → Poly
   | .num k' =>
     let k := (k*k') % c
     bif k == 0 then
       .num 0
     else
       .add k m (.num 0)
   | .add k' m' p =>
     let k := (k*k') % c
     bif k == 0 then
       go p
     else
       .add k (m.mul m') (go p)

def Poly.combineC (p₁ p₂ : Poly) (c : Nat) : Poly :=
  go hugeFuel p₁ p₂
where
  go (fuel : Nat) (p₁ p₂ : Poly) : Poly :=
    match fuel with
    | 0 => p₁.concat p₂
    | fuel + 1 => match p₁, p₂ with
      | .num k₁, .num k₂ => .num ((k₁ + k₂) % c)
      | .num k₁, .add k₂ m₂ p₂ => addConstC (.add k₂ m₂ p₂) k₁ c
      | .add k₁ m₁ p₁, .num k₂ => addConstC (.add k₁ m₁ p₁) k₂ c
      | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
        match m₁.grevlex m₂ with
        | .eq =>
          let k := (k₁ + k₂) % c
          bif k == 0 then
            go fuel p₁ p₂
          else
            .add k m₁ (go fuel p₁ p₂)
        | .gt => .add k₁ m₁ (go fuel p₁ (.add k₂ m₂ p₂))
        | .lt => .add k₂ m₂ (go fuel (.add k₁ m₁ p₁) p₂)

def Poly.mulC (p₁ : Poly) (p₂ : Poly) (c : Nat) : Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | .num k => acc.combineC (p₂.mulConstC k c) c
    | .add k m p₁ => go p₁ (acc.combineC (p₂.mulMonC k m c) c)

def Poly.powC (p : Poly) (k : Nat) (c : Nat) : Poly :=
  match k with
  | 0 => .num 1
  | 1 => p
  | k+1 => p.mulC (powC p k c) c

def Expr.toPolyC (e : Expr) (c : Nat) : Poly :=
  go e
where
  go : Expr → Poly
    | .num n   => .num (n % c)
    | .var x   => Poly.ofVar x
    | .add a b => (go a).combineC (go b) c
    | .mul a b => (go a).mulC (go b) c
    | .neg a   => (go a).mulConstC (-1) c
    | .sub a b => (go a).combineC ((go b).mulConstC (-1) c) c
    | .pow a k =>
      match a with
      | .num n => .num ((n^k) % c)
      | .var x => Poly.ofMon (.mult {x, k} .unit)
      | _ => (go a).powC k c

/--
A Nullstellensatz certificate.
```
lhs₁ = rh₁ → ... → lhsₙ = rhₙ → q₁*(lhs₁ - rhs₁) + ... + qₙ*(lhsₙ - rhsₙ) = 0
```
-/
inductive NullCert where
  | empty
  | add (q : Poly) (lhs : Expr) (rhs : Expr) (s : NullCert)

/--
```
q₁*(lhs₁ - rhs₁) + ... + qₙ*(lhsₙ - rhsₙ)
```
-/
def NullCert.denote {α} [CommRing α] (ctx : Context α) : NullCert → α
  | .empty => 0
  | .add q lhs rhs nc => (q.denote ctx)*(lhs.denote ctx - rhs.denote ctx) + nc.denote ctx

/--
```
lhs₁ = rh₁ → ... → lhsₙ = rhₙ → p
```
-/
def NullCert.eqsImplies {α} [CommRing α] (ctx : Context α) (nc : NullCert) (p : Prop) : Prop :=
  match nc with
  | .empty           => p
  | .add _ lhs rhs nc => lhs.denote ctx = rhs.denote ctx → eqsImplies ctx nc p

/--
A polynomial representing
```
q₁*(lhs₁ - rhs₁) + ... + qₙ*(lhsₙ - rhsₙ)
```
-/
def NullCert.toPoly (nc : NullCert) : Poly :=
  match nc with
  | .empty => .num 0
  | .add q lhs rhs nc => (q.mul (lhs.sub rhs).toPoly).combine nc.toPoly

def NullCert.toPolyC (nc : NullCert) (c : Nat) : Poly :=
  match nc with
  | .empty => .num 0
  | .add q lhs rhs nc => (q.mulC ((lhs.sub rhs).toPolyC c) c).combineC (nc.toPolyC c) c

/-!
Theorems for justifying the procedure for commutative rings in `grind`.
-/

theorem denoteInt_eq {α} [CommRing α] (k : Int) : denoteInt (α := α) k = k := by
  simp [denoteInt, cond_eq_if] <;> split
  next h => rw [ofNat_eq_natCast, ← intCast_natCast, ← intCast_neg, ← Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt h)]
  next h => rw [ofNat_eq_natCast, ← intCast_natCast, ← Int.eq_natAbs_of_nonneg (Int.le_of_not_gt h)]

theorem Power.denote_eq {α} [CommRing α] (ctx : Context α) (p : Power)
    : p.denote ctx = p.x.denote ctx ^ p.k := by
  cases p <;> simp [Power.denote] <;> split <;> simp [pow_zero, pow_succ, one_mul]

theorem Mon.denote_ofVar {α} [CommRing α] (ctx : Context α) (x : Var)
    : denote ctx (ofVar x) = x.denote ctx := by
  simp [denote, ofVar, Power.denote_eq, pow_succ, pow_zero, one_mul, mul_one]

theorem Mon.denote_concat {α} [CommRing α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (concat m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  induction m₁ <;> simp [concat, denote, one_mul, *]
  next p₁ m₁ ih => rw [mul_assoc]

private theorem le_of_blt_false {a b : Nat} : a.blt b = false → b ≤ a := by
  intro h; apply Nat.le_of_not_gt; show ¬a < b
  rw [← Nat.blt_eq, h]; simp

private theorem eq_of_blt_false {a b : Nat} : a.blt b = false → b.blt a = false → a = b := by
  intro h₁ h₂
  replace h₁ := le_of_blt_false h₁
  replace h₂ := le_of_blt_false h₂
  exact Nat.le_antisymm h₂ h₁

theorem Mon.denote_mulPow {α} [CommRing α] (ctx : Context α) (p : Power) (m : Mon)
    : denote ctx (mulPow p m) = p.denote ctx * m.denote ctx := by
  fun_induction mulPow <;> simp [mulPow, denote, mul_assoc, mul_comm, mul_left_comm, *]
  next h₁ h₂ =>
    have := eq_of_blt_false h₁ h₂
    simp [denote, Power.denote_eq, pow_add, this, mul_assoc]

theorem Mon.denote_mul {α} [CommRing α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (mul m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  unfold mul
  generalize hugeFuel = fuel
  fun_induction mul.go
    <;> simp [mul.go, denote, denote_concat, denote_mulPow, one_mul, mul_one,
      mul_assoc, mul_left_comm, mul_comm, *]
  next h₁ h₂ _ =>
    have := eq_of_blt_false h₁ h₂
    simp [Power.denote_eq, pow_add, mul_assoc, mul_left_comm, mul_comm, this]

theorem Var.eq_of_revlex {x₁ x₂ : Var} : x₁.revlex x₂ = .eq → x₁ = x₂ := by
  simp [revlex, cond_eq_if] <;> split <;> simp
  next h₁ => intro h₂; exact Nat.le_antisymm h₂ (Nat.ge_of_not_lt h₁)

theorem eq_of_powerRevlex {k₁ k₂ : Nat} : powerRevlex k₁ k₂ = .eq → k₁ = k₂ := by
  simp [powerRevlex, cond_eq_if] <;> split <;> simp
  next h₁ => intro h₂; exact Nat.le_antisymm h₂ (Nat.ge_of_not_lt h₁)

theorem Power.eq_of_revlex (p₁ p₂ : Power) : p₁.revlex p₂ = .eq → p₁ = p₂ := by
  cases p₁; cases p₂; simp [revlex, Ordering.then]; split
  next h₁ => intro h₂; simp [Var.eq_of_revlex h₁, eq_of_powerRevlex h₂]
  next h₁ => intro h₂; simp [h₂] at h₁

private theorem then_gt (o : Ordering) : ¬ o.then .gt = .eq := by
  cases o <;> simp [Ordering.then]

private theorem then_lt (o : Ordering) : ¬ o.then .lt = .eq := by
  cases o <;> simp [Ordering.then]

private theorem then_eq (o₁ o₂ : Ordering) : o₁.then o₂ = .eq ↔ o₁ = .eq ∧ o₂ = .eq := by
  cases o₁ <;> cases o₂ <;> simp [Ordering.then]

theorem Mon.eq_of_revlexWF {m₁ m₂ : Mon} : m₁.revlexWF m₂ = .eq → m₁ = m₂ := by
  fun_induction revlexWF <;> simp [revlexWF, *, then_gt, then_lt, then_eq]
  next p₁ m₁ p₂ m₂ h ih =>
    cases p₁; cases p₂; intro h₁ h₂; simp [ih h₁, h]
    simp at h h₂
    simp [h, eq_of_powerRevlex h₂]

theorem Mon.eq_of_revlexFuel {fuel : Nat} {m₁ m₂ : Mon} : revlexFuel fuel m₁ m₂ = .eq → m₁ = m₂ := by
  fun_induction revlexFuel <;> simp [revlexFuel, *, then_gt, then_lt, then_eq]
  next => apply eq_of_revlexWF
  next p₁ m₁ p₂ m₂ h ih =>
    cases p₁; cases p₂; intro h₁ h₂; simp [ih h₁, h]
    simp at h h₂
    simp [h, eq_of_powerRevlex h₂]

theorem Mon.eq_of_revlex {m₁ m₂ : Mon} : revlex m₁ m₂ = .eq → m₁ = m₂ := by
  apply eq_of_revlexFuel

theorem Mon.eq_of_grevlex {m₁ m₂ : Mon} : grevlex m₁ m₂ = .eq → m₁ = m₂ := by
  simp [grevlex, then_eq]; intro; apply eq_of_revlex

theorem Poly.denote_ofMon {α} [CommRing α] (ctx : Context α) (m : Mon)
    : denote ctx (ofMon m) = m.denote ctx := by
  simp [ofMon, denote, intCast_one, intCast_zero, one_mul, add_zero]

theorem Poly.denote_ofVar {α} [CommRing α] (ctx : Context α) (x : Var)
    : denote ctx (ofVar x) = x.denote ctx := by
  simp [ofVar, denote_ofMon, Mon.denote_ofVar]

theorem Poly.denote_addConst {α} [CommRing α] (ctx : Context α) (p : Poly) (k : Int) : (addConst p k).denote ctx = p.denote ctx + k := by
  simp [addConst, cond_eq_if]; split
  next => simp [*, intCast_zero, add_zero]
  next =>
    fun_induction addConst.go <;> simp [addConst.go, denote, *]
    next => rw [intCast_add]
    next => simp [add_comm, add_left_comm, add_assoc]

theorem Poly.denote_insert {α} [CommRing α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (insert k m p).denote ctx = k * m.denote ctx + p.denote ctx := by
  simp [insert, cond_eq_if] <;> split
  next => simp [*, intCast_zero, zero_mul, zero_add]
  next =>
    split
    next h =>
      simp at h <;> simp [*, Mon.denote, denote_addConst, mul_one, add_comm]
    next =>
      fun_induction insert.go <;> simp_all +zetaDelta [insert.go, denote, cond_eq_if]
      next h₁ h₂ =>
        rw [← add_assoc, Mon.eq_of_grevlex h₁, ← right_distrib, ← intCast_add, h₂, intCast_zero, zero_mul, zero_add]
      next h₁ _ =>
        rw [intCast_add, right_distrib, add_assoc, Mon.eq_of_grevlex h₁]
      next =>
        rw [add_left_comm]

theorem Poly.denote_concat {α} [CommRing α] (ctx : Context α) (p₁ p₂ : Poly)
    : (concat p₁ p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  fun_induction concat <;> simp [concat, *, denote_addConst, denote]
  next => rw [add_comm]
  next => rw [add_assoc]

theorem Poly.denote_mulConst {α} [CommRing α] (ctx : Context α) (k : Int) (p : Poly)
    : (mulConst k p).denote ctx = k * p.denote ctx := by
  simp [mulConst, cond_eq_if] <;> split
  next => simp [denote, *, intCast_zero, zero_mul]
  next =>
    split <;> try simp [*, intCast_one, one_mul]
    fun_induction mulConst.go <;> simp [mulConst.go, denote, *]
    next => rw [intCast_mul]
    next => rw [intCast_mul, left_distrib, mul_assoc]

theorem Poly.denote_mulMon {α} [CommRing α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (mulMon k m p).denote ctx = k * m.denote ctx * p.denote ctx := by
  simp [mulMon, cond_eq_if] <;> split
  next => simp [denote, *, intCast_zero, zero_mul]
  next =>
    split
    next h =>
      simp at h; simp [*, Mon.denote, mul_one, denote_mulConst]
    next =>
      fun_induction mulMon.go <;> simp [mulMon.go, denote, *]
      next h => simp +zetaDelta at h; simp [*, intCast_zero, mul_zero]
      next => simp [intCast_mul, intCast_zero, add_zero, mul_comm, mul_left_comm, mul_assoc]
      next => simp [Mon.denote_mul, intCast_mul, left_distrib, mul_comm, mul_left_comm, mul_assoc]

theorem Poly.denote_combine {α} [CommRing α] (ctx : Context α) (p₁ p₂ : Poly)
    : (combine p₁ p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  unfold combine; generalize hugeFuel = fuel
  fun_induction combine.go
    <;> simp [combine.go, *, denote_concat, denote_addConst, denote, intCast_add, cond_eq_if, add_comm, add_left_comm, add_assoc]
  next hg _ h _ =>
    simp +zetaDelta at h; simp [*]
    rw [← add_assoc, Mon.eq_of_grevlex hg, ← right_distrib, ← intCast_add, h, intCast_zero, zero_mul, zero_add]
  next hg _ h _ =>
    simp +zetaDelta at h; simp [*, denote, intCast_add]
    rw [right_distrib, Mon.eq_of_grevlex hg, add_assoc]

theorem Poly.denote_mul_go {α} [CommRing α] (ctx : Context α) (p₁ p₂ acc : Poly)
    : (mul.go p₂ p₁ acc).denote ctx = acc.denote ctx + p₁.denote ctx * p₂.denote ctx := by
  fun_induction mul.go
    <;> simp [mul.go, denote_combine, denote_mulConst, denote, *, right_distrib, denote_mulMon, add_assoc]

theorem Poly.denote_mul {α} [CommRing α] (ctx : Context α) (p₁ p₂ : Poly)
    : (mul p₁ p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  simp [mul, denote_mul_go, denote, intCast_zero, zero_add]

theorem Poly.denote_pow {α} [CommRing α] (ctx : Context α) (p : Poly) (k : Nat)
   : (pow p k).denote ctx = p.denote ctx ^ k := by
 fun_induction pow <;> simp [pow, denote, intCast_one, pow_zero]
 next => simp [pow_succ, pow_zero, one_mul]
 next => simp [denote_mul, *, pow_succ, mul_comm]

theorem Expr.denote_toPoly {α} [CommRing α] (ctx : Context α) (e : Expr)
   : e.toPoly.denote ctx = e.denote ctx := by
  fun_induction toPoly
    <;> simp [toPoly, denote, Poly.denote, Poly.denote_ofVar, Poly.denote_combine,
          Poly.denote_mul, Poly.denote_mulConst, Poly.denote_pow, intCast_pow, intCast_neg, intCast_one,
          neg_mul, one_mul, sub_eq_add_neg, denoteInt_eq, *]
  next => simp [Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one]

theorem Expr.eq_of_toPoly_eq {α} [CommRing α] (ctx : Context α) (a b : Expr) (h : a.toPoly == b.toPoly) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [denote_toPoly] at h
  assumption

def ne_unsat_cert (a b : Expr) : Bool :=
  (a.sub b).toPoly == .num 0

theorem ne_unsat {α} [CommRing α] (ctx : Context α) (a b : Expr)
    : ne_unsat_cert a b → a.denote ctx ≠ b.denote ctx → False := by
  simp [ne_unsat_cert]
  intro h
  replace h := congrArg (Poly.denote ctx .) h
  simp [Poly.denote, Expr.denote, Expr.denote_toPoly, intCast_zero, sub_eq_zero_iff] at h
  assumption

def eq_unsat_cert (a b : Expr) (k : Int) : Bool :=
  k != 0 && (a.sub b).toPoly == .num k

-- Remark: `[IsCharP α 0]` after `(ctx : Context α)` is not a mistake.
-- The `grind` procedure assumes that support theorems start with `{α} [CommRing α] (ctx : Context α)`
theorem eq_unsat {α} [CommRing α] (ctx : Context α) [IsCharP α 0] (a b : Expr) (k : Int)
    : eq_unsat_cert a b k → a.denote ctx = b.denote ctx → False := by
  simp [eq_unsat_cert]
  intro h₁ h₂
  replace h₂ := congrArg (Poly.denote ctx .) h₂
  simp [Poly.denote, Expr.denote, Expr.denote_toPoly, intCast_zero, sub_eq_iff] at h₂
  have := IsCharP.intCast_eq_zero_iff (α := α) 0 k
  simp [h₁] at this
  rw [h₂, Eq.comm, ← sub_eq_iff, sub_self, Eq.comm]
  assumption

/-- Helper theorem for proving `NullCert` theorems. -/
theorem NullCert.eqsImplies_helper {α} [CommRing α] (ctx : Context α) (nc : NullCert) (p : Prop) : (nc.denote ctx = 0 → p) → nc.eqsImplies ctx p := by
  induction nc <;> simp [denote, eqsImplies]
  next ih =>
    intro h₁ h₂
    apply ih
    simp [h₂, sub_self, mul_zero, zero_add] at h₁
    assumption

theorem NullCert.denote_toPoly {α} [CommRing α] (ctx : Context α) (nc : NullCert) : nc.toPoly.denote ctx = nc.denote ctx := by
  induction nc <;> simp [toPoly, denote, Poly.denote, intCast_zero, Poly.denote_combine, Poly.denote_mul, Expr.denote_toPoly, Expr.denote, *]

def NullCert.eq_cert (nc : NullCert) (lhs rhs : Expr) :=
  (lhs.sub rhs).toPoly == nc.toPoly

theorem NullCert.eq {α} [CommRing α] (ctx : Context α) (nc : NullCert) (lhs rhs : Expr)
    : nc.eq_cert lhs rhs → nc.eqsImplies ctx (lhs.denote ctx = rhs.denote ctx) := by
  simp [eq_cert]; intro h₁
  apply eqsImplies_helper
  intro h₂
  replace h₁ := congrArg (Poly.denote ctx) h₁
  simp [Expr.denote_toPoly, denote_toPoly, h₂, Expr.denote, sub_eq_zero_iff] at h₁
  assumption

/-!
Theorems for justifying the procedure for commutative rings with a characteristic in `grind`.
-/

theorem Poly.denote_addConstC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Int) : (addConstC p k c).denote ctx = p.denote ctx + k := by
  fun_induction addConstC <;> simp [addConstC, denote, *]
  next => rw [IsCharP.intCast_emod, intCast_add]
  next => simp [add_comm, add_left_comm, add_assoc]

theorem Poly.denote_insertC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (insertC k m p c).denote ctx = k * m.denote ctx + p.denote ctx := by
  simp [insertC, cond_eq_if] <;> split
  next =>
    rw [← IsCharP.intCast_emod (p := c)]
    simp +zetaDelta [*, intCast_zero, zero_mul, zero_add]
  next =>
    fun_induction insertC.go <;> simp_all +zetaDelta [insertC.go, denote, cond_eq_if]
    next h₁ _ h₂ => rw [IsCharP.intCast_emod]
    next h₁ _ h₂ =>
      rw [← add_assoc, Mon.eq_of_grevlex h₁, ← right_distrib, ← intCast_add, ← IsCharP.intCast_emod (p := c), h₂,
          intCast_zero, zero_mul, zero_add]
    next h₁ _ _ =>
      rw [IsCharP.intCast_emod, intCast_add, right_distrib, add_assoc, Mon.eq_of_grevlex h₁]
    next => rw [IsCharP.intCast_emod]
    next => rw [add_left_comm]

theorem Poly.denote_mulConstC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (p : Poly)
    : (mulConstC k p c).denote ctx = k * p.denote ctx := by
  simp [mulConstC, cond_eq_if] <;> split
  next =>
    rw [← IsCharP.intCast_emod (p := c)]
    simp [denote, *, intCast_zero, zero_mul]
  next =>
    split
    next =>
      rw [← IsCharP.intCast_emod (p := c)]
      simp [*, intCast_one, one_mul]
    next =>
      fun_induction mulConstC.go <;> simp [mulConstC.go, denote, IsCharP.intCast_emod, cond_eq_if, *]
      next => rw [intCast_mul]
      next h _ =>
        simp +zetaDelta at h; simp [*]
        rw [left_distrib, ← mul_assoc, ← intCast_mul, ← IsCharP.intCast_emod (x := k * _) (p := c),
            h, intCast_zero, zero_mul, zero_add]
      next h _ =>
        simp +zetaDelta at h
        simp [*, denote, IsCharP.intCast_emod, intCast_mul, mul_assoc, left_distrib]

theorem Poly.denote_mulMonC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (mulMonC k m p c).denote ctx = k * m.denote ctx * p.denote ctx := by
  simp [mulMonC, cond_eq_if] <;> split
  next =>
    rw [← IsCharP.intCast_emod (p := c)]
    simp [denote, *, intCast_zero, zero_mul]
  next =>
    fun_induction mulMonC.go <;> simp [mulMonC.go, denote, *, cond_eq_if]
    next h =>
      simp +zetaDelta at h; simp [*, denote]
      rw [mul_assoc, mul_left_comm, ← intCast_mul, ← IsCharP.intCast_emod (x := k * _) (p := c), h]
      simp [intCast_zero, mul_zero]
    next h =>
      simp +zetaDelta at h; simp [*, denote, IsCharP.intCast_emod]
      simp [intCast_mul, intCast_zero, add_zero, mul_comm, mul_left_comm, mul_assoc]
    next h _ =>
      simp +zetaDelta at h; simp [*, denote, left_distrib]
      rw [mul_left_comm]
      conv => rhs; rw [← mul_assoc, ← mul_assoc, ← intCast_mul, ← IsCharP.intCast_emod (p := c)]
      rw [Int.mul_comm] at h
      simp [h, intCast_zero, zero_mul, zero_add]
    next h _ =>
      simp +zetaDelta at h
      simp [*, denote, IsCharP.intCast_emod, Mon.denote_mul, intCast_mul, left_distrib,
        mul_comm, mul_left_comm, mul_assoc]

theorem Poly.denote_combineC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ p₂ : Poly)
    : (combineC p₁ p₂ c).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  unfold combineC; generalize hugeFuel = fuel
  fun_induction combineC.go
    <;> simp [combineC.go, *, denote_concat, denote_addConstC, denote, intCast_add,
          cond_eq_if, add_comm, add_left_comm, add_assoc, IsCharP.intCast_emod]
  next hg _ h _ =>
    simp +zetaDelta at h; simp [*]
    rw [← add_assoc, Mon.eq_of_grevlex hg, ← right_distrib, ← intCast_add,
      ← IsCharP.intCast_emod (p := c),
      h, intCast_zero, zero_mul, zero_add]
  next hg _ h _ =>
    simp +zetaDelta at h; simp [*, denote, intCast_add, IsCharP.intCast_emod]
    rw [right_distrib, Mon.eq_of_grevlex hg, add_assoc]

theorem Poly.denote_mulC_go {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ p₂ acc : Poly)
    : (mulC.go p₂ c p₁ acc).denote ctx = acc.denote ctx + p₁.denote ctx * p₂.denote ctx := by
  fun_induction mulC.go
    <;> simp [mulC.go, denote_combineC, denote_mulConstC, denote, *, right_distrib, denote_mulMonC, add_assoc]

theorem Poly.denote_mulC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ p₂ : Poly)
    : (mulC p₁ p₂ c).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  simp [mulC, denote_mulC_go, denote, intCast_zero, zero_add]

theorem Poly.denote_powC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Nat)
   : (powC p k c).denote ctx = p.denote ctx ^ k := by
 fun_induction powC <;> simp [powC, denote, intCast_one, pow_zero]
 next => simp [pow_succ, pow_zero, one_mul]
 next => simp [denote_mulC, *, pow_succ, mul_comm]

theorem Expr.denote_toPolyC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (e : Expr)
   : (e.toPolyC c).denote ctx = e.denote ctx := by
  unfold toPolyC
  fun_induction toPolyC.go
    <;> simp [toPolyC.go, denote, Poly.denote, Poly.denote_ofVar, Poly.denote_combineC,
          Poly.denote_mulC, Poly.denote_mulConstC, Poly.denote_powC, denoteInt_eq, *]
  next => rw [IsCharP.intCast_emod]
  next => rw [intCast_neg, neg_mul, intCast_one, one_mul]
  next => rw [intCast_neg, neg_mul, intCast_one, one_mul, sub_eq_add_neg]
  next => rw [IsCharP.intCast_emod, intCast_pow]
  next => simp [Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one]

theorem Expr.eq_of_toPolyC_eq {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (a b : Expr)
    (h : a.toPolyC c == b.toPolyC c) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [denote_toPolyC] at h
  assumption

def ne_unsatC_cert (a b : Expr) (c : Nat) : Bool :=
  (a.sub b).toPolyC c == .num 0

theorem ne_unsatC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (a b : Expr)
    : ne_unsatC_cert a b c → a.denote ctx ≠ b.denote ctx → False := by
  simp [ne_unsatC_cert]
  intro h
  replace h := congrArg (Poly.denote ctx .) h
  simp [Poly.denote, Expr.denote, Expr.denote_toPolyC, intCast_zero, sub_eq_zero_iff] at h
  assumption

def eq_unsatC_cert (a b : Expr) (c : Nat) (k : Int) : Bool :=
  k != 0 && k % c != 0 && (a.sub b).toPolyC c == .num k

theorem eq_unsatC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (a b : Expr) (k : Int)
    : eq_unsatC_cert a b c k → a.denote ctx = b.denote ctx → False := by
  simp [eq_unsatC_cert]
  intro h₁ h₂ h₃
  replace h₃ := congrArg (Poly.denote ctx .) h₃
  simp [Poly.denote, Expr.denote, Expr.denote_toPolyC, intCast_zero, sub_eq_iff] at h₃
  have := IsCharP.intCast_eq_zero_iff (α := α) c k
  simp [h₁, h₂] at this
  rw [h₃, Eq.comm, ← sub_eq_iff, sub_self, Eq.comm]
  assumption

theorem NullCert.denote_toPolyC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (nc : NullCert) : (nc.toPolyC c).denote ctx = nc.denote ctx := by
  induction nc <;> simp [toPolyC, denote, Poly.denote, intCast_zero, Poly.denote_combineC, Poly.denote_mulC, Expr.denote_toPolyC, Expr.denote, *]

def NullCert.eq_certC (nc : NullCert) (lhs rhs : Expr) (c : Nat) :=
  (lhs.sub rhs).toPolyC c == nc.toPoly

theorem NullCert.eqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (nc : NullCert) (lhs rhs : Expr)
    : nc.eq_certC lhs rhs c → nc.eqsImplies ctx (lhs.denote ctx = rhs.denote ctx) := by
  simp [eq_certC]; intro h₁
  apply eqsImplies_helper
  intro h₂
  replace h₁ := congrArg (Poly.denote ctx) h₁
  simp [Expr.denote_toPolyC, denote_toPoly, h₂, Expr.denote, sub_eq_zero_iff] at h₁
  assumption

end CommRing
end Lean.Grind
