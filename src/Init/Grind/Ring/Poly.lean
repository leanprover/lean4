/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Nat.Lemmas
public import Init.Data.Hashable
public import all Init.Data.Ord
public import Init.Data.RArray
public import Init.Grind.Ring.Basic
public import Init.Grind.Ring.Field
public import Init.Grind.Ordered.Ring
public import Init.GrindInstances.Ring.Int
public section

namespace Lean.Grind
-- These are no longer global instances, so we need to turn them on here.
attribute [local instance] Semiring.natCast Ring.intCast
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
  deriving Inhabited, BEq, Hashable, Repr

abbrev Context (α : Type u) := RArray α

@[expose]
def Var.denote {α} (ctx : Context α) (v : Var) : α :=
  ctx.get v

@[expose]
def denoteInt {α} [Ring α] (k : Int) : α :=
  bif k < 0 then
    - OfNat.ofNat (α := α) k.natAbs
  else
    OfNat.ofNat (α := α) k.natAbs

@[expose]
def Expr.denote {α} [Ring α] (ctx : Context α) : Expr → α
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
  deriving BEq, Repr, Inhabited, Hashable

instance : LawfulBEq Power where
  eq_of_beq {a} := by cases a <;> intro b <;> cases b <;> simp_all! [BEq.beq]
  rfl := by intro a; cases a <;> simp! [BEq.beq]

@[expose]
def Power.varLt (p₁ p₂ : Power) : Bool :=
  p₁.x.blt p₂.x

@[expose]
def Power.denote {α} [Semiring α] (ctx : Context α) : Power → α
  | {x, k} =>
    match k with
    | 0 => 1
    | 1 => x.denote ctx
    | k => x.denote ctx ^ k

inductive Mon where
  | unit
  | mult (p : Power) (m : Mon)
  deriving BEq, Repr, Inhabited, Hashable

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

@[expose]
def Mon.denote {α} [Semiring α] (ctx : Context α) : Mon → α
  | unit => 1
  | .mult p m => p.denote ctx * denote ctx m

@[expose]
def Mon.denote' {α} [Semiring α] (ctx : Context α) (m : Mon) : α :=
  match m with
  | .unit => 1
  | .mult pw m => go m (pw.denote ctx)
where
  go (m : Mon) (acc : α) : α :=
    match m with
    | .unit => acc
    | .mult pw m => go m (acc * (pw.denote ctx))

@[expose]
def Mon.ofVar (x : Var) : Mon :=
  .mult { x, k := 1 } .unit

@[expose]
def Mon.concat (m₁ m₂ : Mon) : Mon :=
  match m₁ with
  | .unit => m₂
  | .mult pw m₁ => .mult pw (concat m₁ m₂)

@[expose]
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

@[expose]
def Mon.length : Mon → Nat
  | .unit => 0
  | .mult _ m => 1 + length m

@[expose]
def hugeFuel := 1000000

@[expose]
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

@[expose]
def Mon.degree : Mon → Nat
  | .unit => 0
  | .mult pw m => pw.k + degree m

@[expose]
def Var.revlex (x y : Var) : Ordering :=
  bif x.blt y then .gt
  else bif y.blt x then .lt
  else .eq

@[expose]
def powerRevlex (k₁ k₂ : Nat) : Ordering :=
  bif k₁.blt k₂ then .gt
  else bif k₂.blt k₁ then .lt
  else .eq

@[expose]
def Power.revlex (p₁ p₂ : Power) : Ordering :=
  p₁.x.revlex p₂.x |>.then (powerRevlex p₁.k p₂.k)

@[expose]
def Mon.revlexWF (m₁ m₂ : Mon) : Ordering :=
  match m₁, m₂ with
  | .unit, .unit => .eq
  | .unit, .mult .. => .gt
  | .mult .., .unit => .lt
  | .mult pw₁ m₁, .mult pw₂ m₂ =>
    bif pw₁.x == pw₂.x then
      revlexWF m₁ m₂ |>.then (powerRevlex pw₁.k pw₂.k)
    else bif pw₁.x.blt pw₂.x then
      revlexWF m₁ (.mult pw₂ m₂) |>.then .lt
    else
      revlexWF (.mult pw₁ m₁) m₂ |>.then .gt

@[expose]
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
        revlexFuel fuel m₁ (.mult pw₂ m₂) |>.then .lt
      else
        revlexFuel fuel (.mult pw₁ m₁) m₂ |>.then .gt

@[expose]
def Mon.revlex (m₁ m₂ : Mon) : Ordering :=
  revlexFuel hugeFuel m₁ m₂

@[expose]
def Mon.grevlex (m₁ m₂ : Mon) : Ordering :=
  compare m₁.degree m₂.degree |>.then (revlex m₁ m₂)

inductive Poly where
  | num (k : Int)
  | add (k : Int) (v : Mon) (p : Poly)
  deriving BEq, Repr, Inhabited, Hashable

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
    change m == m ∧ p == p
    simp [ih]

@[expose]
def Poly.denote [Ring α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => Int.cast k
  | .add k m p => HMul.hMul (α := Int) k (m.denote ctx) + denote ctx p

@[expose]
def Poly.denote' [Ring α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => Int.cast k
  | .add k m p => go p (denoteTerm k m)
where
  denoteTerm (k : Int) (m : Mon) : α :=
    bif k == 1 then
      m.denote' ctx
    else
      HMul.hMul (α := Int) k (m.denote' ctx)

  go (p : Poly) (acc : α) : α :=
    match p with
    | .num 0 => acc
    | .num k => acc + Int.cast k
    | .add k m p => go p (acc + denoteTerm k m)

@[expose]
def Poly.ofMon (m : Mon) : Poly :=
  .add 1 m (.num 0)

@[expose]
def Poly.ofVar (x : Var) : Poly :=
  ofMon (Mon.ofVar x)

@[expose]
def Poly.isSorted : Poly → Bool
  | .num _ => true
  | .add _ _ (.num _) => true
  | .add _ m₁ (.add k m₂ p) => m₁.grevlex m₂ == .gt && (Poly.add k m₂ p).isSorted

@[expose]
def Poly.addConst (p : Poly) (k : Int) : Poly :=
  bif k == 0 then
    p
  else
    go p
where
  go : Poly → Poly
  | .num k' => .num (k' + k)
  | .add k' m p => .add k' m (go p)

@[expose]
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

@[expose]
def Poly.concat (p₁ p₂ : Poly) : Poly :=
  match p₁ with
  | .num k₁ => p₂.addConst k₁
  | .add k m p₁ => .add k m (concat p₁ p₂)

@[expose]
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

@[expose]
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

@[expose]
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

@[expose]
def Poly.mul (p₁ : Poly) (p₂ : Poly) : Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | .num k => acc.combine (p₂.mulConst k)
    | .add k m p₁ => go p₁ (acc.combine (p₂.mulMon k m))

@[expose]
def Poly.pow (p : Poly) (k : Nat) : Poly :=
  match k with
  | 0 => .num 1
  | 1 => p
  | k+1 => p.mul (pow p k)

@[expose]
def Expr.toPoly : Expr → Poly
  | .num n   => .num n
  | .var x   => Poly.ofVar x
  | .add a b => a.toPoly.combine b.toPoly
  | .mul a b => a.toPoly.mul b.toPoly
  | .neg a   => a.toPoly.mulConst (-1)
  | .sub a b => a.toPoly.combine (b.toPoly.mulConst (-1))
  | .pow a k =>
    bif k == 0 then
      .num 1
    else  match a with
    | .num n => .num (n^k)
    | .var x => Poly.ofMon (.mult {x, k} .unit)
    | _ => a.toPoly.pow k

def Poly.normEq0 (p : Poly) (c : Nat) : Poly :=
  match p with
  | .num a =>
    if a % c == 0 then .num 0 else .num a
  | .add a m p =>
    if a % c == 0 then normEq0 p c else .add a m (.normEq0 p c)

/-!
**Definitions for the `IsCharP` case**

We considered using a single set of definitions parameterized by `Option c` or simply set `c = 0` since
`n % 0 = n` in Lean, but decided against it to avoid unnecessary kernel‑reduction overhead.
Once we can specialize definitions before they reach the kernel,
we can merge the two versions. Until then, the `IsCharP` definitions will carry the `C` suffix.
We use them whenever we can infer the characteristic using type class instance synthesis.
-/
@[expose]
def Poly.addConstC (p : Poly) (k : Int) (c : Nat) : Poly :=
  match p with
  | .num k' => .num ((k' + k) % c)
  | .add k' m p => .add k' m (addConstC p k c)

@[expose]
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

@[expose]
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

@[expose]
def Poly.mulMonC (k : Int) (m : Mon) (p : Poly) (c : Nat) : Poly :=
  let k := k % c
  bif k == 0 then
    .num 0
  else bif m == .unit then
    p.mulConstC k c
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

@[expose]
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

@[expose]
def Poly.mulC (p₁ : Poly) (p₂ : Poly) (c : Nat) : Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | .num k => acc.combineC (p₂.mulConstC k c) c
    | .add k m p₁ => go p₁ (acc.combineC (p₂.mulMonC k m c) c)

@[expose]
def Poly.powC (p : Poly) (k : Nat) (c : Nat) : Poly :=
  match k with
  | 0 => .num 1
  | 1 => p
  | k+1 => p.mulC (powC p k c) c

@[expose]
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
      bif k == 0 then
        .num 1
      else match a with
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
@[expose]
def NullCert.denote {α} [CommRing α] (ctx : Context α) : NullCert → α
  | .empty => 0
  | .add q lhs rhs nc => (q.denote ctx)*(lhs.denote ctx - rhs.denote ctx) + nc.denote ctx

/--
```
lhs₁ = rh₁ → ... → lhsₙ = rhₙ → p
```
-/
@[expose]
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
@[expose]
def NullCert.toPoly (nc : NullCert) : Poly :=
  match nc with
  | .empty => .num 0
  | .add q lhs rhs nc => (q.mul (lhs.sub rhs).toPoly).combine nc.toPoly

@[expose]
def NullCert.toPolyC (nc : NullCert) (c : Nat) : Poly :=
  match nc with
  | .empty => .num 0
  | .add q lhs rhs nc => (q.mulC ((lhs.sub rhs).toPolyC c) c).combineC (nc.toPolyC c) c

/-!
Theorems for justifying the procedure for commutative rings in `grind`.
-/

open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg
open CommSemiring

theorem denoteInt_eq {α} [CommRing α] (k : Int) : denoteInt (α := α) k = k := by
  simp [denoteInt, cond_eq_if] <;> split
  next h => rw [ofNat_eq_natCast, ← intCast_natCast, ← intCast_neg, ← Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt h)]
  next h => rw [ofNat_eq_natCast, ← intCast_natCast, ← Int.eq_natAbs_of_nonneg (Int.le_of_not_gt h)]

theorem Power.denote_eq {α} [Semiring α] (ctx : Context α) (p : Power)
    : p.denote ctx = p.x.denote ctx ^ p.k := by
  cases p <;> simp [Power.denote] <;> split <;> simp [pow_zero, pow_succ, one_mul]

theorem Mon.denote'_eq_denote {α} [Semiring α] (ctx : Context α) (m : Mon) : m.denote' ctx = m.denote ctx := by
  cases m <;> simp [denote', denote]
  next pw m =>
  generalize pw.denote ctx = acc
  fun_induction denote'.go
  next => simp [denote, Semiring.mul_one]
  next acc pw m ih => simp [ih, denote, Semiring.mul_assoc]

theorem Mon.denote_ofVar {α} [Semiring α] (ctx : Context α) (x : Var)
    : denote ctx (ofVar x) = x.denote ctx := by
  simp [denote, ofVar, Power.denote_eq, pow_succ, pow_zero, one_mul, mul_one]

theorem Mon.denote_concat {α} [Semiring α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (concat m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  induction m₁ <;> simp [concat, denote, one_mul, *]
  next p₁ m₁ ih => rw [mul_assoc]

private theorem le_of_blt_false {a b : Nat} : a.blt b = false → b ≤ a := by
  intro h; apply Nat.le_of_not_gt; change ¬a < b
  rw [← Nat.blt_eq, h]; simp

private theorem eq_of_blt_false {a b : Nat} : a.blt b = false → b.blt a = false → a = b := by
  intro h₁ h₂
  replace h₁ := le_of_blt_false h₁
  replace h₂ := le_of_blt_false h₂
  exact Nat.le_antisymm h₂ h₁

theorem Mon.denote_mulPow {α} [CommSemiring α] (ctx : Context α) (p : Power) (m : Mon)
    : denote ctx (mulPow p m) = p.denote ctx * m.denote ctx := by
  fun_induction mulPow <;> simp [denote, mul_left_comm, *]
  next h₁ h₂ =>
    have := eq_of_blt_false h₁ h₂
    simp [Power.denote_eq, pow_add, mul_assoc, this]

theorem Mon.denote_mul {α} [CommSemiring α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (mul m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  unfold mul
  generalize hugeFuel = fuel
  fun_induction mul.go
    <;> simp [denote, denote_concat, one_mul,
      mul_assoc, mul_left_comm, CommSemiring.mul_comm, *]
  next h₁ h₂ _ =>
    have := eq_of_blt_false h₁ h₂
    simp [Power.denote_eq, pow_add, this]

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
  fun_induction revlexWF <;> simp [*]
  next p₁ m₁ p₂ m₂ h ih =>
    cases p₁; cases p₂; intro h₁ h₂; simp [ih h₁]
    simp at h h₂
    simp [h, eq_of_powerRevlex h₂]

theorem Mon.eq_of_revlexFuel {fuel : Nat} {m₁ m₂ : Mon} : revlexFuel fuel m₁ m₂ = .eq → m₁ = m₂ := by
  fun_induction revlexFuel
  case case1 => apply eq_of_revlexWF
  case case5 p₁ m₁ p₂ m₂ h ih =>
    simp
    cases p₁; cases p₂; intro h₁ h₂; simp [ih h₁]
    simp at h h₂
    simp [h, eq_of_powerRevlex h₂]
  all_goals simp

theorem Mon.eq_of_revlex {m₁ m₂ : Mon} : revlex m₁ m₂ = .eq → m₁ = m₂ := by
  apply eq_of_revlexFuel

theorem Mon.eq_of_grevlex {m₁ m₂ : Mon} : grevlex m₁ m₂ = .eq → m₁ = m₂ := by
  simp [grevlex]; intro; apply eq_of_revlex

theorem Poly.denoteTerm_eq  {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) : denote'.denoteTerm ctx k m = k * m.denote ctx := by
  simp [denote'.denoteTerm, Mon.denote'_eq_denote, cond_eq_if, zsmul_eq_intCast_mul]; intro; subst k; rw [Ring.intCast_one, Semiring.one_mul]

theorem Poly.denote'_eq_denote {α} [Ring α] (ctx : Context α) (p : Poly) : p.denote' ctx = p.denote ctx := by
  cases p <;> simp [denote', denote, denoteTerm_eq, zsmul_eq_intCast_mul]
  next k m p =>
    generalize k * m.denote ctx = acc
    fun_induction denote'.go <;> simp [denote, *, Ring.intCast_zero, Semiring.add_zero, denoteTerm_eq]
    next ih => simp [denoteTerm_eq] at ih; simp [ih, Semiring.add_assoc, zsmul_eq_intCast_mul]

theorem Poly.denote_ofMon {α} [CommRing α] (ctx : Context α) (m : Mon)
    : denote ctx (ofMon m) = m.denote ctx := by
  simp [ofMon, denote, intCast_one, intCast_zero, one_mul, add_zero, zsmul_eq_intCast_mul]

theorem Poly.denote_ofVar {α} [CommRing α] (ctx : Context α) (x : Var)
    : denote ctx (ofVar x) = x.denote ctx := by
  simp [ofVar, denote_ofMon, Mon.denote_ofVar]

theorem Poly.denote_addConst {α} [CommRing α] (ctx : Context α) (p : Poly) (k : Int) : (addConst p k).denote ctx = p.denote ctx + k := by
  simp [addConst, cond_eq_if]; split
  next => simp [*, intCast_zero, add_zero]
  next =>
    fun_induction addConst.go <;> simp [denote, *]
    next => rw [intCast_add]
    next => simp [add_comm, add_left_comm]

theorem Poly.denote_insert {α} [CommRing α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (insert k m p).denote ctx = k * m.denote ctx + p.denote ctx := by
  simp [insert, cond_eq_if] <;> split
  next => simp [*, intCast_zero, zero_mul, zero_add]
  next =>
    split
    next h =>
      simp at h <;> simp [*, Mon.denote, denote_addConst, mul_one, add_comm]
    next =>
      fun_induction insert.go <;> simp_all +zetaDelta [denote, zsmul_eq_intCast_mul]
      next h₁ h₂ =>
        rw [← add_assoc, Mon.eq_of_grevlex h₁, ← right_distrib, ← intCast_add, h₂, intCast_zero, zero_mul, zero_add]
      next h₁ _ =>
        rw [intCast_add, right_distrib, add_assoc, Mon.eq_of_grevlex h₁]
      next =>
        rw [add_left_comm]

theorem Poly.denote_concat {α} [CommRing α] (ctx : Context α) (p₁ p₂ : Poly)
    : (concat p₁ p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  fun_induction concat <;> simp [*, denote_addConst, denote]
  next => rw [add_comm]
  next => rw [add_assoc]

theorem Poly.denote_mulConst {α} [CommRing α] (ctx : Context α) (k : Int) (p : Poly)
    : (mulConst k p).denote ctx = k * p.denote ctx := by
  simp [mulConst, cond_eq_if] <;> split
  next => simp [denote, *, intCast_zero, zero_mul]
  next =>
    split <;> try simp [*, intCast_one, one_mul]
    fun_induction mulConst.go <;> simp [denote, *]
    next => rw [intCast_mul]
    next => rw [left_distrib, ← zsmul_eq_intCast_mul, ← zsmul_eq_intCast_mul, mul_zsmul]

theorem Poly.denote_mulMon {α} [CommRing α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (mulMon k m p).denote ctx = k * m.denote ctx * p.denote ctx := by
  simp [mulMon, cond_eq_if] <;> split
  next => simp [denote, *, intCast_zero, zero_mul]
  next =>
    split
    next h =>
      simp at h; simp [*, Mon.denote, mul_one, denote_mulConst]
    next =>
      fun_induction mulMon.go <;> simp [denote, zsmul_eq_intCast_mul, *]
      next h => simp +zetaDelta at h; simp [*, intCast_zero, mul_zero]
      next => simp [intCast_mul, intCast_zero, add_zero, mul_comm, mul_left_comm, mul_assoc]
      next => simp [Mon.denote_mul, intCast_mul, left_distrib, mul_left_comm, mul_assoc]

theorem Poly.denote_combine {α} [CommRing α] (ctx : Context α) (p₁ p₂ : Poly)
    : (combine p₁ p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  unfold combine; generalize hugeFuel = fuel
  fun_induction combine.go
    <;> simp [*, denote_concat, denote_addConst, denote, intCast_add, add_comm, add_left_comm, add_assoc, zsmul_eq_intCast_mul]
  case case5 hg _ h _ =>
    simp +zetaDelta at h
    rw [← add_assoc, Mon.eq_of_grevlex hg, ← right_distrib, ← intCast_add, h, intCast_zero, zero_mul, zero_add]
  case case6 hg k h _ =>
    simp +zetaDelta [intCast_add]
    rw [right_distrib, Mon.eq_of_grevlex hg, add_assoc]

theorem Poly.denote_mul_go {α} [CommRing α] (ctx : Context α) (p₁ p₂ acc : Poly)
    : (mul.go p₂ p₁ acc).denote ctx = acc.denote ctx + p₁.denote ctx * p₂.denote ctx := by
  fun_induction mul.go
    <;> simp [denote_combine, denote_mulConst, denote, *, right_distrib, denote_mulMon, add_assoc, zsmul_eq_intCast_mul]

theorem Poly.denote_mul {α} [CommRing α] (ctx : Context α) (p₁ p₂ : Poly)
    : (mul p₁ p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  simp [mul, denote_mul_go, denote, intCast_zero, zero_add]

theorem Poly.denote_pow {α} [CommRing α] (ctx : Context α) (p : Poly) (k : Nat)
   : (pow p k).denote ctx = p.denote ctx ^ k := by
 fun_induction pow
 next => simp [denote, intCast_one, pow_zero]
 next => simp [pow_succ, pow_zero, one_mul]
 next => simp [denote_mul, *, pow_succ, mul_comm]

theorem Expr.denote_toPoly {α} [CommRing α] (ctx : Context α) (e : Expr)
   : e.toPoly.denote ctx = e.denote ctx := by
  fun_induction toPoly
    <;> simp [denote, Poly.denote, Poly.denote_ofVar, Poly.denote_combine,
          Poly.denote_mul, Poly.denote_mulConst, Poly.denote_pow, intCast_pow, intCast_neg, intCast_one,
          neg_mul, one_mul, sub_eq_add_neg, denoteInt_eq, *]
  next a k h => simp at h; simp [h, Semiring.pow_zero]
  next => simp [Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one]

theorem Expr.eq_of_toPoly_eq {α} [CommRing α] (ctx : Context α) (a b : Expr) (h : a.toPoly == b.toPoly) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [denote_toPoly] at h
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

@[expose]
def NullCert.eq_cert (nc : NullCert) (lhs rhs : Expr) :=
  (lhs.sub rhs).toPoly == nc.toPoly

theorem NullCert.eq {α} [CommRing α] (ctx : Context α) (nc : NullCert) {lhs rhs : Expr}
    : nc.eq_cert lhs rhs → nc.eqsImplies ctx (lhs.denote ctx = rhs.denote ctx) := by
  simp [eq_cert]; intro h₁
  apply eqsImplies_helper
  intro h₂
  replace h₁ := congrArg (Poly.denote ctx) h₁
  simp [Expr.denote_toPoly, denote_toPoly, h₂, Expr.denote, sub_eq_zero_iff] at h₁
  assumption

theorem NullCert.eqsImplies_helper' {α} [CommRing α] {ctx : Context α} {nc : NullCert} {p q : Prop} : nc.eqsImplies ctx p → (p → q) → nc.eqsImplies ctx q := by
  induction nc <;> simp [eqsImplies]
  next => intro h₁ h₂; exact h₂ h₁
  next ih => intro h₁ h₂ h₃; exact ih (h₁ h₃) h₂

theorem NullCert.ne_unsat {α} [CommRing α] (ctx : Context α) (nc : NullCert) (lhs rhs : Expr)
    : nc.eq_cert lhs rhs → lhs.denote ctx ≠ rhs.denote ctx → nc.eqsImplies ctx False := by
  intro h₁ h₂
  exact eqsImplies_helper' (eq ctx nc h₁) h₂

@[expose]
def NullCert.eq_nzdiv_cert (nc : NullCert) (k : Int) (lhs rhs : Expr) : Bool :=
  k ≠ 0 && (lhs.sub rhs).toPoly.mulConst k == nc.toPoly

theorem NullCert.eq_nzdiv {α} [CommRing α] [NoNatZeroDivisors α] (ctx : Context α) (nc : NullCert) (k : Int) (lhs rhs : Expr)
    : nc.eq_nzdiv_cert k lhs rhs → nc.eqsImplies ctx (lhs.denote ctx = rhs.denote ctx) := by
  simp [eq_nzdiv_cert]
  intro h₁ h₂
  apply eqsImplies_helper
  intro h₃
  replace h₂ := congrArg (Poly.denote ctx) h₂
  simp [Expr.denote_toPoly, Poly.denote_mulConst, denote_toPoly, h₃, Expr.denote, ← zsmul_eq_intCast_mul] at h₂
  replace h₂ := no_int_zero_divisors h₁ h₂
  rw [sub_eq_zero_iff] at h₂
  assumption

theorem NullCert.ne_nzdiv_unsat {α} [CommRing α] [NoNatZeroDivisors α] (ctx : Context α) (nc : NullCert) (k : Int) (lhs rhs : Expr)
    : nc.eq_nzdiv_cert k lhs rhs → lhs.denote ctx ≠ rhs.denote ctx → nc.eqsImplies ctx False := by
  intro h₁ h₂
  exact eqsImplies_helper' (eq_nzdiv ctx nc k lhs rhs h₁) h₂

@[expose]
def NullCert.eq_unsat_cert (nc : NullCert) (k : Int) : Bool :=
  k ≠ 0 && nc.toPoly == .num k

theorem NullCert.eq_unsat {α} [CommRing α] [IsCharP α 0] (ctx : Context α) (nc : NullCert) (k : Int)
    : nc.eq_unsat_cert k → nc.eqsImplies ctx False := by
  simp [eq_unsat_cert]
  intro h₁ h₂
  apply eqsImplies_helper
  intro h₃
  replace h₂ := congrArg (Poly.denote ctx) h₂
  simp [denote_toPoly, h₃, Poly.denote] at h₂
  have := IsCharP.intCast_eq_zero_iff (α := α) 0 k
  simp [← h₂] at this
  contradiction

/-!
Theorems for justifying the procedure for commutative rings with a characteristic in `grind`.
-/

theorem Poly.denote_addConstC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Int) : (addConstC p k c).denote ctx = p.denote ctx + k := by
  fun_induction addConstC <;> simp [denote, *]
  next => rw [IsCharP.intCast_emod, intCast_add]
  next => simp [add_comm, add_left_comm]

theorem Poly.denote_insertC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (insertC k m p c).denote ctx = k * m.denote ctx + p.denote ctx := by
  simp [insertC, cond_eq_if] <;> split
  next =>
    rw [← IsCharP.intCast_emod (p := c)]
    simp +zetaDelta [*, intCast_zero, zero_mul, zero_add]
  next =>
    fun_induction insertC.go <;> simp_all +zetaDelta [denote, zsmul_eq_intCast_mul]
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
      fun_induction mulConstC.go <;> simp [denote, IsCharP.intCast_emod, *]
      next => rw [intCast_mul]
      next h _ =>
        simp +zetaDelta at h
        rw [left_distrib, zsmul_eq_intCast_mul, ← mul_assoc, ← intCast_mul, ← IsCharP.intCast_emod (x := k * _) (p := c),
            h, intCast_zero, zero_mul, zero_add]
      next h _ =>
        simp +zetaDelta [IsCharP.intCast_emod, intCast_mul, mul_assoc, left_distrib, zsmul_eq_intCast_mul]

theorem Poly.denote_mulMonC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (mulMonC k m p c).denote ctx = k * m.denote ctx * p.denote ctx := by
  simp [mulMonC, cond_eq_if] <;> split
  next =>
    rw [← IsCharP.intCast_emod (p := c)]
    simp [denote, *, intCast_zero, zero_mul]
  next =>
    split
    next h =>
      simp at h; simp [*, Mon.denote, mul_one, denote_mulConstC, IsCharP.intCast_emod]
    next =>
      fun_induction mulMonC.go <;> simp [denote]
      next h =>
        simp +zetaDelta at h
        rw [mul_assoc, mul_left_comm, ← intCast_mul, ← IsCharP.intCast_emod (x := k * _) (p := c), h]
        simp [intCast_zero, mul_zero]
      next h =>
        simp +zetaDelta [IsCharP.intCast_emod, intCast_mul, intCast_zero, add_zero, mul_comm, mul_left_comm, mul_assoc, zsmul_eq_intCast_mul]
      next h _ =>
        simp +zetaDelta at h; simp [*, left_distrib, zsmul_eq_intCast_mul]
        rw [mul_left_comm]
        conv => rhs; rw [← mul_assoc, ← mul_assoc, ← intCast_mul, ← IsCharP.intCast_emod (p := c)]
        rw [Int.mul_comm] at h
        simp [h, intCast_zero, zero_mul, zero_add]
      next h _ =>
        simp +zetaDelta [*, IsCharP.intCast_emod, Mon.denote_mul, intCast_mul, left_distrib,
          mul_left_comm, mul_assoc, zsmul_eq_intCast_mul]

theorem Poly.denote_combineC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ p₂ : Poly)
    : (combineC p₁ p₂ c).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  unfold combineC; generalize hugeFuel = fuel
  fun_induction combineC.go
    <;> simp [*, denote_concat, denote_addConstC, denote, intCast_add,
          add_comm, add_left_comm, add_assoc, IsCharP.intCast_emod, zsmul_eq_intCast_mul]
  next hg _ h _ =>
    simp +zetaDelta at h
    rw [← add_assoc, Mon.eq_of_grevlex hg, ← right_distrib, ← intCast_add,
      ← IsCharP.intCast_emod (p := c),
      h, intCast_zero, zero_mul, zero_add]
  next hg _ h _ =>
    simp +zetaDelta only [IsCharP.intCast_emod, intCast_add]
    rw [right_distrib, Mon.eq_of_grevlex hg, add_assoc]

theorem Poly.denote_mulC_go {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ p₂ acc : Poly)
    : (mulC.go p₂ c p₁ acc).denote ctx = acc.denote ctx + p₁.denote ctx * p₂.denote ctx := by
  fun_induction mulC.go
    <;> simp [denote_combineC, denote_mulConstC, denote, *, right_distrib, denote_mulMonC, add_assoc, zsmul_eq_intCast_mul]

theorem Poly.denote_mulC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ p₂ : Poly)
    : (mulC p₁ p₂ c).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  simp [mulC, denote_mulC_go, denote, intCast_zero, zero_add]

theorem Poly.denote_powC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Nat)
   : (powC p k c).denote ctx = p.denote ctx ^ k := by
 fun_induction powC
 next => simp [denote, intCast_one, pow_zero]
 next => simp [pow_succ, pow_zero, one_mul]
 next => simp [denote_mulC, *, pow_succ, mul_comm]

theorem Expr.denote_toPolyC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (e : Expr)
   : (e.toPolyC c).denote ctx = e.denote ctx := by
  unfold toPolyC
  fun_induction toPolyC.go
    <;> simp [denote, Poly.denote, Poly.denote_ofVar, Poly.denote_combineC,
          Poly.denote_mulC, Poly.denote_mulConstC, Poly.denote_powC, denoteInt_eq, *]
  next => rw [IsCharP.intCast_emod]
  next => rw [intCast_neg, neg_mul, intCast_one, one_mul]
  next => rw [intCast_neg, neg_mul, intCast_one, one_mul, sub_eq_add_neg]
  next a k h => simp at h; simp [h, Semiring.pow_zero, Ring.intCast_one]
  next => rw [IsCharP.intCast_emod, intCast_pow]
  next => simp [Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one]

theorem Expr.eq_of_toPolyC_eq {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (a b : Expr)
    (h : a.toPolyC c == b.toPolyC c) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [denote_toPolyC] at h
  assumption

theorem NullCert.denote_toPolyC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (nc : NullCert) : (nc.toPolyC c).denote ctx = nc.denote ctx := by
  induction nc <;> simp [toPolyC, denote, Poly.denote, intCast_zero, Poly.denote_combineC, Poly.denote_mulC, Expr.denote_toPolyC, Expr.denote, *]

@[expose]
def NullCert.eq_certC (nc : NullCert) (lhs rhs : Expr) (c : Nat) :=
  (lhs.sub rhs).toPolyC c == nc.toPolyC c

theorem NullCert.eqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (nc : NullCert) {lhs rhs : Expr}
    : nc.eq_certC lhs rhs c → nc.eqsImplies ctx (lhs.denote ctx = rhs.denote ctx) := by
  simp [eq_certC]; intro h₁
  apply eqsImplies_helper
  intro h₂
  replace h₁ := congrArg (Poly.denote ctx) h₁
  simp [Expr.denote_toPolyC, denote_toPolyC, h₂, Expr.denote, sub_eq_zero_iff] at h₁
  assumption

theorem NullCert.ne_unsatC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (nc : NullCert) (lhs rhs : Expr)
    : nc.eq_certC lhs rhs c → lhs.denote ctx ≠ rhs.denote ctx → nc.eqsImplies ctx False := by
  intro h₁ h₂
  exact eqsImplies_helper' (eqC ctx nc h₁) h₂

@[expose]
def NullCert.eq_nzdiv_certC (nc : NullCert) (k : Int) (lhs rhs : Expr) (c : Nat) : Bool :=
  k ≠ 0 && ((lhs.sub rhs).toPolyC c).mulConstC k c == nc.toPolyC c

theorem NullCert.eq_nzdivC {α c} [CommRing α] [IsCharP α c] [NoNatZeroDivisors α] (ctx : Context α) (nc : NullCert) (k : Int) (lhs rhs : Expr)
    : nc.eq_nzdiv_certC k lhs rhs c → nc.eqsImplies ctx (lhs.denote ctx = rhs.denote ctx) := by
  simp [eq_nzdiv_certC]
  intro h₁ h₂
  apply eqsImplies_helper
  intro h₃
  replace h₂ := congrArg (Poly.denote ctx) h₂
  simp [Expr.denote_toPolyC, Poly.denote_mulConstC, denote_toPolyC, h₃, Expr.denote, ← zsmul_eq_intCast_mul] at h₂
  replace h₂ := no_int_zero_divisors h₁ h₂
  rw [sub_eq_zero_iff] at h₂
  assumption

theorem NullCert.ne_nzdiv_unsatC {α c} [CommRing α] [IsCharP α c] [NoNatZeroDivisors α] (ctx : Context α) (nc : NullCert) (k : Int) (lhs rhs : Expr)
    : nc.eq_nzdiv_certC k lhs rhs c → lhs.denote ctx ≠ rhs.denote ctx → nc.eqsImplies ctx False := by
  intro h₁ h₂
  exact eqsImplies_helper' (eq_nzdivC ctx nc k lhs rhs h₁) h₂

@[expose]
def NullCert.eq_unsat_certC (nc : NullCert) (k : Int) (c : Nat) : Bool :=
  k % c != 0 && nc.toPolyC c == .num k

theorem NullCert.eq_unsatC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (nc : NullCert) (k : Int)
    : nc.eq_unsat_certC k c → nc.eqsImplies ctx False := by
  simp [eq_unsat_certC]
  intro h₁ h₂
  apply eqsImplies_helper
  intro h₃
  replace h₂ := congrArg (Poly.denote ctx) h₂
  simp [denote_toPolyC, h₃, Poly.denote] at h₂
  have := IsCharP.intCast_eq_zero_iff (α := α) c k
  simp [h₂] at this
  contradiction

namespace Stepwise
/-!
Theorems for stepwise proof-term construction
-/
@[expose]
def core_cert (lhs rhs : Expr) (p : Poly) : Bool :=
  (lhs.sub rhs).toPoly == p

theorem core {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  simp [core_cert]; intro; subst p
  simp [Expr.denote_toPoly, Expr.denote]
  simp [sub_eq_zero_iff]

@[expose]
def superpose_cert (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) : Bool :=
  (p₁.mulMon k₁ m₁).combine (p₂.mulMon k₂ m₂) == p

theorem superpose {α} [CommRing α] (ctx : Context α) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : superpose_cert k₁ m₁ p₁ k₂ m₂ p₂ p → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [superpose_cert]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combine, Poly.denote_mulMon, h₁, h₂, mul_zero, add_zero]

@[expose]
def simp_cert (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) : Bool :=
  (p₁.mulConst k₁).combine (p₂.mulMon k₂ m₂) == p

theorem simp {α} [CommRing α] (ctx : Context α) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : simp_cert k₁ p₁ k₂ m₂ p₂ p → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [simp_cert]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combine, Poly.denote_mulMon, Poly.denote_mulConst, h₁, h₂, mul_zero, add_zero]

@[expose]
def mul_cert (p₁ : Poly) (k : Int) (p : Poly) : Bool :=
  p₁.mulConst k == p

@[expose]
def mul {α} [CommRing α] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_cert p₁ k p → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [mul_cert]; intro _ h; subst p
  simp [Poly.denote_mulConst, *, mul_zero]

@[expose]
def div_cert (p₁ : Poly) (k : Int) (p : Poly) : Bool :=
  k != 0 && p.mulConst k == p₁

@[expose]
def div {α} [CommRing α] (ctx : Context α) [NoNatZeroDivisors α] (p₁ : Poly) (k : Int) (p : Poly)
    : div_cert p₁ k p → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [div_cert]; intro hnz _ h; subst p₁
  simp [Poly.denote_mulConst, ← zsmul_eq_intCast_mul] at h
  exact no_int_zero_divisors hnz h

@[expose]
def unsat_eq_cert (p : Poly) (k : Int) : Bool :=
  k != 0 && p == .num k

@[expose]
def unsat_eq {α} [CommRing α] (ctx : Context α) [IsCharP α 0] (p : Poly) (k : Int)
    : unsat_eq_cert p k → p.denote ctx = 0 → False := by
  simp [unsat_eq_cert]; intro h _; subst p; simp [Poly.denote]
  have := IsCharP.intCast_eq_zero_iff (α := α) 0 k
  simp [h] at this
  assumption

theorem d_init {α} [CommRing α] (ctx : Context α) (p : Poly) : (1:Int) * p.denote ctx = p.denote ctx := by
  rw [intCast_one, one_mul]

@[expose]
def d_step1_cert (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) : Bool :=
  p == p₁.combine (p₂.mulMon k₂ m₂)

theorem d_step1 {α} [CommRing α] (ctx : Context α) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : d_step1_cert p₁ k₂ m₂ p₂ p → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  simp [d_step1_cert]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combine, Poly.denote_mulMon, h₂, mul_zero, add_zero, h₁]

@[expose]
def d_stepk_cert (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) : Bool :=
  p == (p₁.mulConst k₁).combine (p₂.mulMon k₂ m₂)

theorem d_stepk {α} [CommRing α] (ctx : Context α) (k₁ : Int) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : d_stepk_cert k₁ p₁ k₂ m₂ p₂ p → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → (k₁*k : Int) * init.denote ctx = p.denote ctx := by
  simp [d_stepk_cert]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combine, Poly.denote_mulMon, Poly.denote_mulConst, h₂, mul_zero, add_zero]
  rw [intCast_mul, mul_assoc, h₁]

@[expose]
def imp_1eq_cert (lhs rhs : Expr) (p₁ p₂ : Poly) : Bool :=
  (lhs.sub rhs).toPoly == p₁ && p₂ == .num 0

theorem imp_1eq {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_1eq_cert lhs rhs p₁ p₂ → (1:Int) * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_1eq_cert, intCast_one, one_mul]; intro _ _; subst p₁ p₂
  simp [Expr.denote_toPoly, Expr.denote, sub_eq_zero_iff, Poly.denote, intCast_zero]

@[expose]
def imp_keq_cert (lhs rhs : Expr) (k : Int) (p₁ p₂ : Poly) : Bool :=
  k != 0 && (lhs.sub rhs).toPoly == p₁ && p₂ == .num 0

theorem imp_keq  {α} [CommRing α] (ctx : Context α) [NoNatZeroDivisors α] (k : Int) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_keq_cert lhs rhs k p₁ p₂ → k * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_keq_cert]; intro hnz _ _; subst p₁ p₂
  simp [Expr.denote_toPoly, Expr.denote, Poly.denote, intCast_zero, ← zsmul_eq_intCast_mul]
  intro h; replace h := no_int_zero_divisors hnz h
  rw [← sub_eq_zero_iff, h]

@[expose]
def core_certC (lhs rhs : Expr) (p : Poly) (c : Nat) : Bool :=
  (lhs.sub rhs).toPolyC c == p

theorem coreC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_certC lhs rhs p c → lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  simp [core_certC]; intro; subst p
  simp [Expr.denote_toPolyC, Expr.denote]
  simp [sub_eq_zero_iff]

@[expose]
def superpose_certC (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (c : Nat) : Bool :=
  (p₁.mulMonC k₁ m₁ c).combineC (p₂.mulMonC k₂ m₂ c) c == p

theorem superposeC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : superpose_certC k₁ m₁ p₁ k₂ m₂ p₂ p c → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [superpose_certC]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combineC, Poly.denote_mulMonC, h₁, h₂, mul_zero, add_zero]

@[expose]
def mul_certC (p₁ : Poly) (k : Int) (p : Poly) (c : Nat) : Bool :=
  p₁.mulConstC k c == p

@[expose]
def mulC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_certC p₁ k p c → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [mul_certC]; intro _ h; subst p
  simp [Poly.denote_mulConstC, *, mul_zero]

@[expose]
def div_certC (p₁ : Poly) (k : Int) (p : Poly) (c : Nat) : Bool :=
  k != 0 && p.mulConstC k c == p₁

@[expose]
def divC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) [NoNatZeroDivisors α] (p₁ : Poly) (k : Int) (p : Poly)
    : div_certC p₁ k p c → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [div_certC]; intro hnz _ h; subst p₁
  simp [Poly.denote_mulConstC, ← zsmul_eq_intCast_mul] at h
  exact no_int_zero_divisors hnz h

@[expose]
def simp_certC (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (c : Nat) : Bool :=
  (p₁.mulConstC k₁ c).combineC (p₂.mulMonC k₂ m₂ c) c == p

theorem simpC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : simp_certC k₁ p₁ k₂ m₂ p₂ p c → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [simp_certC]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combineC, Poly.denote_mulMonC, Poly.denote_mulConstC, h₁, h₂, mul_zero, add_zero]

@[expose]
def unsat_eq_certC (p : Poly) (k : Int) (c : Nat) : Bool :=
  k % c != 0 && p == .num k

@[expose]
def unsat_eqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Int)
    : unsat_eq_certC p k c → p.denote ctx = 0 → False := by
  simp [unsat_eq_certC]; intro h _; subst p; simp [Poly.denote]
  have := IsCharP.intCast_eq_zero_iff (α := α) c k
  simp [h] at this
  assumption

@[expose]
def d_step1_certC (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (c : Nat) : Bool :=
  p == p₁.combineC (p₂.mulMonC k₂ m₂ c) c

theorem d_step1C {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : d_step1_certC p₁ k₂ m₂ p₂ p c → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  simp [d_step1_certC]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combineC, Poly.denote_mulMonC, h₂, mul_zero, add_zero, h₁]

@[expose]
def d_stepk_certC (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (c : Nat) : Bool :=
  p == (p₁.mulConstC k₁ c).combineC (p₂.mulMonC k₂ m₂ c) c

theorem d_stepkC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : d_stepk_certC k₁ p₁ k₂ m₂ p₂ p c → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → (k₁*k : Int) * init.denote ctx = p.denote ctx := by
  simp [d_stepk_certC]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combineC, Poly.denote_mulMonC, Poly.denote_mulConstC, h₂, mul_zero, add_zero]
  rw [intCast_mul, mul_assoc, h₁]

@[expose]
def imp_1eq_certC (lhs rhs : Expr) (p₁ p₂ : Poly) (c : Nat) : Bool :=
  (lhs.sub rhs).toPolyC c == p₁ && p₂ == .num 0

theorem imp_1eqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_1eq_certC lhs rhs p₁ p₂ c → (1:Int) * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_1eq_certC, intCast_one, one_mul]; intro _ _; subst p₁ p₂
  simp [Expr.denote_toPolyC, Expr.denote, sub_eq_zero_iff, Poly.denote, intCast_zero]

@[expose]
def imp_keq_certC (lhs rhs : Expr) (k : Int) (p₁ p₂ : Poly) (c : Nat) : Bool :=
  k != 0 && (lhs.sub rhs).toPolyC c == p₁ && p₂ == .num 0

theorem imp_keqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) [NoNatZeroDivisors α] (k : Int) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_keq_certC lhs rhs k p₁ p₂ c → k * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_keq_certC]; intro hnz _ _; subst p₁ p₂
  simp [Expr.denote_toPolyC, Expr.denote, Poly.denote, intCast_zero, ← zsmul_eq_intCast_mul]
  intro h; replace h := no_int_zero_divisors hnz h
  rw [← sub_eq_zero_iff, h]

end Stepwise

/-! IntModule interface -/

@[expose]
def Mon.denoteAsIntModule [CommRing α] (ctx : Context α) (m : Mon) : α :=
  match m with
  | .unit => One.one
  | .mult pw m => go m (pw.denote ctx)
where
  go (m : Mon) (acc : α) : α :=
    match m with
    | .unit => acc
    | .mult pw m => go m (acc * pw.denote ctx)

@[expose]
def Poly.denoteAsIntModule [CommRing α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => HMul.hMul (α := Int) k (One.one : α)
  | .add k m p => HMul.hMul (α := Int) k (m.denoteAsIntModule ctx) + denoteAsIntModule ctx p

theorem Mon.denoteAsIntModule_go_eq_denote {α} [CommRing α] (ctx : Context α) (m : Mon) (acc : α)
    : denoteAsIntModule.go ctx m acc = acc * m.denote ctx := by
  induction m generalizing acc <;> simp [*, denoteAsIntModule.go, denote, mul_one, *, mul_assoc]

theorem Mon.denoteAsIntModule_eq_denote {α} [CommRing α] (ctx : Context α) (m : Mon)
    : m.denoteAsIntModule ctx = m.denote ctx := by
  cases m <;> simp [denoteAsIntModule, denote, denoteAsIntModule_go_eq_denote]; rfl

theorem Poly.denoteAsIntModule_eq_denote {α} [CommRing α] (ctx : Context α) (p : Poly) : p.denoteAsIntModule ctx = p.denote ctx := by
  induction p <;> simp [*, denoteAsIntModule, denote, mul_one, One.one, Mon.denoteAsIntModule_eq_denote, Ring.zsmul_eq_intCast_mul]

open Stepwise

theorem eq_norm {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx = rhs.denote ctx → p.denoteAsIntModule ctx = 0 := by
  rw [Poly.denoteAsIntModule_eq_denote]; apply core

theorem diseq_norm {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx ≠ rhs.denote ctx → p.denoteAsIntModule ctx ≠ 0 := by
  simp [core_cert, Poly.denoteAsIntModule_eq_denote]; intro _ h; subst p; simp [Expr.denote_toPoly, Expr.denote]
  intro h; rw [sub_eq_zero_iff] at h; contradiction

open OrderedAdd

theorem le_norm {α} [CommRing α] [Preorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx ≤ rhs.denote ctx → p.denoteAsIntModule ctx ≤ 0 := by
  simp [core_cert, Poly.denoteAsIntModule_eq_denote]; intro _ h; subst p; simp [Expr.denote_toPoly, Expr.denote]
  replace h := add_le_left h ((-1) * rhs.denote ctx)
  rw [neg_mul, ← sub_eq_add_neg, one_mul, ← sub_eq_add_neg, sub_self] at h
  assumption

theorem lt_norm {α} [CommRing α] [Preorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx < rhs.denote ctx → p.denoteAsIntModule ctx < 0 := by
  simp [core_cert, Poly.denoteAsIntModule_eq_denote]; intro _ h; subst p; simp [Expr.denote_toPoly, Expr.denote]
  replace h := add_lt_left h ((-1) * rhs.denote ctx)
  rw [neg_mul, ← sub_eq_add_neg, one_mul, ← sub_eq_add_neg, sub_self] at h
  assumption

theorem not_le_norm {α} [CommRing α] [LinearOrder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert rhs lhs p → ¬ lhs.denote ctx ≤ rhs.denote ctx → p.denoteAsIntModule ctx < 0 := by
  simp [core_cert, Poly.denoteAsIntModule_eq_denote]; intro _ h₁; subst p; simp [Expr.denote_toPoly, Expr.denote]
  replace h₁ := LinearOrder.lt_of_not_le h₁
  replace h₁ := add_lt_left h₁ (-lhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem not_lt_norm {α} [CommRing α] [LinearOrder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert rhs lhs p → ¬ lhs.denote ctx < rhs.denote ctx → p.denoteAsIntModule ctx ≤ 0 := by
  simp [core_cert, Poly.denoteAsIntModule_eq_denote]; intro _ h₁; subst p; simp [Expr.denote_toPoly, Expr.denote]
  replace h₁ := LinearOrder.le_of_not_lt h₁
  replace h₁ := add_le_left h₁ (-lhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem not_le_norm' {α} [CommRing α] [Preorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → ¬ lhs.denote ctx ≤ rhs.denote ctx → ¬ p.denoteAsIntModule ctx ≤ 0 := by
  simp [core_cert, Poly.denoteAsIntModule_eq_denote]; intro _ h₁; subst p; simp [Expr.denote_toPoly, Expr.denote]; intro h
  replace h := add_le_right (rhs.denote ctx) h
  rw [sub_eq_add_neg, add_left_comm, ← sub_eq_add_neg, sub_self] at h; simp [add_zero] at h
  contradiction

theorem not_lt_norm' {α} [CommRing α] [Preorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → ¬ lhs.denote ctx < rhs.denote ctx → ¬ p.denoteAsIntModule ctx < 0 := by
  simp [core_cert, Poly.denoteAsIntModule_eq_denote]; intro _ h₁; subst p; simp [Expr.denote_toPoly, Expr.denote]; intro h
  replace h := add_lt_right (rhs.denote ctx) h
  rw [sub_eq_add_neg, add_left_comm, ← sub_eq_add_neg, sub_self] at h; simp [add_zero] at h
  contradiction

theorem inv_int_eq [Field α] [IsCharP α 0] (b : Int) : b != 0 → (denoteInt b : α) * (denoteInt b)⁻¹ = 1 := by
  simp; intro h
  have : (denoteInt b : α) ≠ 0 := by
    simp [denoteInt_eq]; intro h
    have := IsCharP.intCast_eq_zero_iff (α := α) 0 b; simp [*] at this
  rw [Field.mul_inv_cancel this]

theorem inv_int_eqC {α c} [Field α] [IsCharP α c] (b : Int) : b % c != 0 → (denoteInt b : α) * (denoteInt b)⁻¹ = 1 := by
  simp; intro h
  have : (denoteInt b : α) ≠ 0 := by
    simp [denoteInt_eq]; intro h
    have := IsCharP.intCast_eq_zero_iff (α := α) c b; simp [*] at this
  rw [Field.mul_inv_cancel this]

theorem inv_zero_eqC {α c} [Field α] [IsCharP α c] (b : Int) : b % c == 0 → (denoteInt b : α)⁻¹ = 0 := by
  simp [denoteInt_eq]; intro h
  have : (b : α) = 0 := by
    have := IsCharP.intCast_eq_zero_iff (α := α) c b
    simp [*]
  simp [this, Field.inv_zero]

open Classical in
theorem inv_split {α} [Field α] (a : α) : if a = 0 then a⁻¹ = 0 else a * a⁻¹ = 1 := by
  split
  next h => simp [h, Field.inv_zero]
  next h => rw [Field.mul_inv_cancel h]

@[expose]
def one_eq_zero_unsat_cert (p : Poly) :=
  p == .num 1 || p == .num (-1)

theorem one_eq_zero_unsat {α} [Field α] (ctx : Context α) (p : Poly) : one_eq_zero_unsat_cert p → p.denote ctx = 0 → False := by
  simp [one_eq_zero_unsat_cert]; intro h; cases h <;> simp [*, Poly.denote, intCast_one, intCast_neg]
  next => rw [Eq.comm]; apply Field.zero_ne_one
  next => rw [← neg_eq_zero, neg_neg, Eq.comm]; apply Field.zero_ne_one

theorem diseq_to_eq {α} [Field α] (a b : α) : a ≠ b → (a - b)*(a - b)⁻¹ = 1 := by
  intro h
  have : a - b ≠ 0 := by
    intro h'; rw [sub_eq_zero_iff.mp h'] at h
    contradiction
  exact Field.mul_inv_cancel this

theorem diseq0_to_eq {α} [Field α] (a : α) : a ≠ 0 → a*a⁻¹ = 1 := by
  exact Field.mul_inv_cancel

/-! normEq0 helper theorems -/

private theorem of_mod_eq_0 {α} [CommRing α] {a : Int} {c : Nat} : Int.cast c = (0 : α) → a % c = 0 → (a : α) = 0 := by
  intro h h'
  have := Int.ediv_add_emod a ↑c
  rw [h', Int.add_zero] at this
  replace this := congrArg (Int.cast (R := α)) this
  rw [Ring.intCast_mul] at this
  rw [← Ring.intCast_ofNat] at h
  rw [h, Ring.intCast_zero, Semiring.zero_mul] at this
  rw [this]

theorem Poly.normEq0_eq {α} [CommRing α] (ctx : Context α) (p : Poly) (c : Nat) (h : Int.cast c = (0 : α)) : (p.normEq0 c).denote ctx = p.denote ctx := by
  induction p
  next a =>
    simp [denote, normEq0]; split <;> simp [denote]
    next h' => rw [of_mod_eq_0 h h', Ring.intCast_zero]
  next a m p ih =>
    simp [denote, normEq0]; split <;> simp [denote, zsmul_eq_intCast_mul, *]
    next h' => rw [of_mod_eq_0 h h', Semiring.zero_mul, zero_add]

@[expose]
def eq_normEq0_cert (c : Nat) (p₁ p₂ p : Poly) : Bool :=
  p₁ == .num c && p == p₂.normEq0 c

theorem eq_normEq0 {α} [CommRing α] (ctx : Context α) (c : Nat) (p₁ p₂ p : Poly)
    : eq_normEq0_cert c p₁ p₂ p → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [eq_normEq0_cert]; intro _ _; subst p₁ p; simp [Poly.denote]; intro h₁ h₂
  rw [p₂.normEq0_eq] <;> assumption

theorem gcd_eq_0 [CommRing α] (g n m a b : Int) (h : g = a * n + b * m)
    (h₁ : Int.cast (R := α) n = 0) (h₂ : Int.cast (R := α) m = 0) : Int.cast (R := α) g = 0 := by
  rw [← Ring.intCast_ofNat] at *
  replace h₁ := congrArg (Int.cast (R := α) a * ·) h₁; simp at h₁
  rw [← Ring.intCast_mul, Ring.intCast_zero, Semiring.mul_zero] at h₁
  replace h₂ := congrArg (Int.cast (R := α) b * ·) h₂; simp at h₂
  rw [← Ring.intCast_mul, Ring.intCast_zero, Semiring.mul_zero] at h₂
  replace h₁ := congrArg (· + Int.cast (b * m)) h₁; simp at h₁
  rw [← Ring.intCast_add, h₂, zero_add, ← h] at h₁
  rw [Ring.intCast_zero, h₁]

@[expose]
def eq_gcd_cert (a b : Int) (p₁ p₂ p : Poly) : Bool :=
  match p₁ with
  | .add .. => false
  | .num n =>
  match p₂ with
  | .add .. => false
  | .num m =>
  match p with
  | .add .. => false
  | .num g => g == a * n + b * m

theorem eq_gcd {α} [CommRing α] (ctx : Context α) (a b : Int) (p₁ p₂ p : Poly)
    : eq_gcd_cert a b p₁ p₂ p → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [eq_gcd_cert]; cases p₁ <;> cases p₂ <;> cases p <;> simp [Poly.denote]
  next n m g =>
  apply gcd_eq_0 g n m a b

@[expose]
def d_normEq0_cert (c : Nat) (p₁ p₂ p : Poly) : Bool :=
  p₂ == .num c && p == p₁.normEq0 c

theorem d_normEq0 {α} [CommRing α] (ctx : Context α) (k : Int) (c : Nat) (init : Poly) (p₁ p₂ p : Poly)
    : d_normEq0_cert c p₁ p₂ p → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  simp [d_normEq0_cert]; intro _ h₁ h₂; subst p p₂; simp [Poly.denote]
  intro h; rw [p₁.normEq0_eq] <;> assumption

@[expose] def norm_int_cert (e : Expr) (p : Poly) : Bool :=
  e.toPoly == p

theorem norm_int (ctx : Context Int) (e : Expr) (p : Poly) : norm_int_cert e p → e.denote ctx = p.denote' ctx := by
  simp [norm_int_cert, Poly.denote'_eq_denote]; intro; subst p; simp [Expr.denote_toPoly]

end CommRing
end Lean.Grind
