/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Ord.Basic
public import Init.Grind.Ring.Field
public import Init.Grind.Ordered.Ring
public import Init.GrindInstances.Ring.Int
import all Init.Data.Ord.Basic
import Init.LawfulBEqTactics
public import Init.Classical
public import Init.Data.Bool
public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.RArray
public import Init.Ext
import Init.Data.Hashable
import Init.Data.Int.LemmasAux
import Init.Data.Int.Order
import Init.Data.Nat.Linear
import Init.Grind.Ordered.Order
import Init.Omega

@[expose] public section

namespace Lean.Grind.CommRing
/-!
Data-structures, definitions and theorems for implementing the
`grind` solver and normalizer for commutative rings and its extensions (e.g., fields,
commutative semirings, etc.)

The solver uses proof-by-reflection.
-/
open Std
-- These are no longer global instances, so we need to turn them on here.
attribute [local instance] Semiring.natCast Ring.intCast
abbrev Var := Nat

inductive Expr where
  | num  (k : Int)
  | natCast (k : Nat)
  | intCast (k : Int)
  | var  (i : Var)
  | neg (a : Expr)
  | add  (a b : Expr)
  | sub  (a b : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (k : Nat)
  deriving Inhabited, BEq, Hashable, Repr

abbrev Context (α : Type u) := RArray α

set_option allowUnsafeReducibility true

abbrev Var.denote {α} (ctx : Context α) (v : Var) : α :=
  ctx.get v

noncomputable abbrev denoteInt {α} [Ring α] (k : Int) : α :=
  Bool.rec
    (OfNat.ofNat (α := α) k.natAbs)
    (- OfNat.ofNat (α := α) k.natAbs)
    (Int.blt' k 0)

noncomputable abbrev Expr.denote {α} [Ring α] (ctx : Context α) (e : Expr) : α :=
  Expr.rec
    (fun k => denoteInt k)
    (fun k => NatCast.natCast (R := α) k)
    (fun k => IntCast.intCast (R := α) k)
    (fun x => x.denote ctx)
    (fun _ ih => - ih)
    (fun _ _ ih₁ ih₂ => ih₁ + ih₂)
    (fun _ _ ih₁ ih₂ => ih₁ - ih₂)
    (fun _ _ ih₁ ih₂ => ih₁ * ih₂)
    (fun _ k ih => ih ^ k)
    e

attribute [semireducible] Var.denote denoteInt Expr.denote

structure Power where
  x : Var
  k : Nat
  deriving BEq, ReflBEq, LawfulBEq, Repr, Inhabited, Hashable

protected noncomputable def Power.beq' (pw₁ pw₂ : Power) : Bool :=
  Power.rec (fun x₁ k₁ => Power.rec (fun x₂ k₂ => Nat.beq x₁ x₂ && Nat.beq k₁ k₂) pw₂) pw₁

@[simp] theorem Power.beq'_eq (pw₁ pw₂ : Power) : pw₁.beq' pw₂ = (pw₁ = pw₂) := by
  cases pw₁; cases pw₂; simp [Power.beq']

def Power.varLt (p₁ p₂ : Power) : Bool :=
  p₁.x.blt p₂.x

abbrev Power.denote {α} [Semiring α] (ctx : Context α) : Power → α
  | {x, k} =>
    match k with
    | 0 => 1
    | 1 => x.denote ctx
    | k => x.denote ctx ^ k

attribute [semireducible] Power.denote

inductive Mon where
  | unit
  | mult (p : Power) (m : Mon)
  deriving BEq, ReflBEq, LawfulBEq, Repr, Inhabited, Hashable

protected noncomputable def Mon.beq' (m₁ : Mon) : Mon → Bool :=
  Mon.rec
    (fun m₂ => Mon.rec true (fun _ _ _ => false) m₂)
    (fun pw₁ _ ih m₂ => Mon.rec false (fun pw₂ m₂ _ => (Power.beq' pw₁ pw₂).and' (ih m₂)) m₂) m₁

@[simp] theorem Mon.beq'_eq (m₁ m₂ : Mon) : m₁.beq' m₂ = (m₁ = m₂) := by
  induction m₁ generalizing m₂ <;> cases m₂ <;> simp [Mon.beq']
  rename_i pw₁ _ ih _ m₂
  intro; subst pw₁
  simp [← ih m₂, ← Bool.and'_eq_and]
  rfl

abbrev Mon.denote {α} [Semiring α] (ctx : Context α) : Mon → α
  | unit => 1
  | .mult p m => p.denote ctx * denote ctx m

abbrev Mon.denote'.go [Semiring α] (ctx : Context α) (m : Mon) (acc : α) : α :=
  match m with
  | .unit => acc
  | .mult pw m => go ctx m (acc * (pw.denote ctx))

abbrev Mon.denote' {α} [Semiring α] (ctx : Context α) (m : Mon) : α :=
  match m with
  | .unit => 1
  | .mult pw m => denote'.go ctx m (pw.denote ctx)

attribute [semireducible] Mon.denote Mon.denote' Mon.denote'.go

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

-- **Note**: We use the `_nc` suffix for functions for the non-commutative case

def Mon.mulPow_nc (pw : Power) (m : Mon) : Mon :=
  match m with
  | .unit      => .mult pw .unit
  | .mult pw' m =>
    bif pw.x == pw'.x then
      .mult { x := pw.x, k := pw.k + pw'.k } m
    else
      .mult pw (.mult pw' m)

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

noncomputable def Mon.mul_k : Mon → Mon → Mon :=
  Nat.rec
    (fun m₁ m₂ => concat m₁ m₂)
    (fun _ ih m₁ m₂ =>
      Mon.rec (t := m₂)
        m₁
        (fun pw₂ m₂' _ => Mon.rec (t := m₁)
          m₂
          (fun pw₁ m₁' _ =>
            Bool.rec (t := pw₁.varLt pw₂)
              (Bool.rec (t := pw₂.varLt pw₁)
                (.mult { x := pw₁.x, k := Nat.add pw₁.k pw₂.k } (ih m₁' m₂'))
                (.mult pw₂ (ih (.mult pw₁ m₁') m₂')))
              (.mult pw₁ (ih m₁' (.mult pw₂ m₂'))))))
    hugeFuel

theorem Mon.mul_k_eq_mul : Mon.mul_k m₁ m₂ = Mon.mul m₁ m₂ := by
  unfold mul_k mul
  generalize hugeFuel = fuel
  fun_induction mul.go
  · rfl
  · rfl
  case case3 m₂ _ =>
    cases m₂
    · contradiction
    · dsimp
  case case4 fuel pw₁ m₁ pw₂ m₂ h ih =>
    dsimp only
    rw [h]
    dsimp only
    rw [ih]
  case case5 fuel pw₁ m₁ pw₂ m₂ h₁ h₂ ih =>
    dsimp only
    rw [h₁]
    dsimp only
    rw [h₂]
    dsimp only
    rw [ih]
  case case6 fuel pw₁ m₁ pw₂ m₂ h₁ h₂ ih =>
    dsimp only
    rw [h₁]
    dsimp only
    rw [h₂]
    dsimp only
    rw [ih]
    rfl

def Mon.mul_nc (m₁ m₂ : Mon) : Mon :=
  match m₁ with
  | .unit          => m₂
  | .mult pw .unit => m₂.mulPow_nc pw
  | .mult pw m₁    => .mult pw (mul_nc m₁ m₂)

def Mon.degree : Mon → Nat
  | .unit => 0
  | .mult pw m => pw.k + degree m

noncomputable def Mon.degree_k : Mon → Nat :=
  Nat.rec
    (fun m => m.degree)
    (fun _ ih m =>
      Mon.rec (t := m)
        0
        (fun pw m' _ => Nat.add pw.k (ih m')))
    hugeFuel

theorem Mon.degree_k_eq_degree : Mon.degree_k m = Mon.degree m := by
  unfold degree_k
  generalize hugeFuel = fuel
  induction fuel generalizing m with
  | zero => rfl
  | succ fuel ih =>
    conv => rhs; unfold degree
    split
    · rfl
    · dsimp only
      rw [← ih]
      rfl

def Var.revlex (x y : Var) : Ordering :=
  bif x.blt y then .gt
  else bif y.blt x then .lt
  else .eq

def powerRevlex (k₁ k₂ : Nat) : Ordering :=
  bif k₁.blt k₂ then .gt
  else bif k₂.blt k₁ then .lt
  else .eq

noncomputable def powerRevlex_k (k₁ k₂ : Nat) : Ordering :=
  Bool.rec (Bool.rec .eq .lt (Nat.blt k₂ k₁)) .gt (Nat.blt k₁ k₂)

theorem powerRevlex_k_eq_powerRevlex (k₁ k₂ : Nat) : powerRevlex_k k₁ k₂ = powerRevlex k₁ k₂ := by
  simp [powerRevlex_k, powerRevlex, cond] <;> split <;> simp [*]
  split <;> simp [*]

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
      revlexWF m₁ (.mult pw₂ m₂) |>.then .lt
    else
      revlexWF (.mult pw₁ m₁) m₂ |>.then .gt

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

def Mon.revlex (m₁ m₂ : Mon) : Ordering :=
  revlexFuel hugeFuel m₁ m₂

def Mon.grevlex (m₁ m₂ : Mon) : Ordering :=
  compare m₁.degree m₂.degree |>.then (revlex m₁ m₂)

noncomputable def Mon.revlex_k : Mon → Mon → Ordering :=
  Nat.rec
    revlexWF
    (fun _ ih m₁ => Mon.rec
      (fun m₂ => Mon.rec .eq (fun _ _ _ => .gt) m₂)
      (fun pw₁ m₁ _ m₂ => Mon.rec
        .lt
        (fun pw₂ m₂ _ => Bool.rec
          (Bool.rec
            (ih (.mult pw₁ m₁) m₂ |>.then' .gt)
            (ih m₁ (.mult pw₂ m₂) |>.then' .lt)
            (pw₁.x.blt pw₂.x))
          (ih m₁ m₂ |>.then' (powerRevlex_k pw₁.k pw₂.k))
          (Nat.beq pw₁.x pw₂.x))
        m₂)
      m₁)
    hugeFuel

noncomputable def Mon.grevlex_k (m₁ m₂ : Mon) : Ordering :=
  Bool.rec
    (Bool.rec .gt .lt (Nat.blt m₁.degree m₂.degree))
    (revlex_k m₁ m₂)
    (Nat.beq m₁.degree_k m₂.degree_k)

theorem Mon.revlex_k_eq_revlex (m₁ m₂ : Mon) : m₁.revlex_k m₂ = m₁.revlex m₂ := by
  unfold revlex_k revlex
  generalize hugeFuel = fuel
  induction fuel generalizing m₁ m₂
  next => rfl
  next =>
    simp [revlexFuel]; split <;> try rfl
    next ih _ _ pw₁ m₁ pw₂ m₂ =>
      simp only [cond_eq_ite, beq_iff_eq]
      split
      next h =>
        replace h : Nat.beq pw₁.x pw₂.x = true := by rw [Nat.beq_eq, h]
        simp [h, ← ih m₁ m₂, Ordering.then'_eq_then, powerRevlex_k_eq_powerRevlex]
      next h =>
        replace h : Nat.beq pw₁.x pw₂.x = false := by
          rw [← Bool.not_eq_true, Nat.beq_eq]; exact h
        simp only [h]
        split
        next h => simp [h, ← ih m₁ (mult pw₂ m₂), Ordering.then'_eq_then]
        next h =>
          rw [Bool.not_eq_true] at h
          simp [h, ← ih (mult pw₁ m₁) m₂, Ordering.then'_eq_then]

theorem Mon.grevlex_k_eq_grevlex (m₁ m₂ : Mon) : m₁.grevlex_k m₂ = m₁.grevlex m₂ := by
  unfold grevlex_k grevlex; simp [revlex_k_eq_revlex]
  simp [*, compare, compareOfLessAndEq]
  split
  next h =>
    have h₁ : Nat.blt m₁.degree m₂.degree = true := by simp [h]
    have h₂ : Nat.beq m₁.degree m₂.degree = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; omega
    simp [degree_k_eq_degree, h₁, h₂]
  next h =>
    split
    next h' =>
      have h₂ : Nat.beq m₁.degree m₂.degree = true := by rw [Nat.beq_eq, h']
      simp [degree_k_eq_degree, h₂]
    next h' =>
      have h₁ : Nat.blt m₁.degree m₂.degree = false := by
        rw [← Bool.not_eq_true, Nat.blt_eq]; assumption
      have h₂ : Nat.beq m₁.degree m₂.degree = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]; assumption
      simp [degree_k_eq_degree, h₁, h₂]

inductive Poly where
  | num (k : Int)
  | add (k : Int) (v : Mon) (p : Poly)
  deriving BEq, ReflBEq, LawfulBEq, Repr, Inhabited, Hashable

protected noncomputable def Poly.beq' (p₁ : Poly) : Poly → Bool :=
  Poly.rec
    (fun k₁ p₂ => Poly.rec (fun k₂ => Int.beq' k₁ k₂) (fun _ _ _ _ => false) p₂)
    (fun k₁ v₁ _ ih p₂ =>
      Poly.rec
        (fun _ => false)
        (fun k₂ v₂ p₂ _ => (Int.beq' k₁ k₂).and' ((Mon.beq' v₁ v₂).and' (ih p₂))) p₂)
    p₁

@[simp] theorem Poly.beq'_eq (p₁ p₂ : Poly) : p₁.beq' p₂ = (p₁ = p₂) := by
  induction p₁ generalizing p₂ <;> cases p₂ <;> simp [Poly.beq']
  rename_i k₁ m₁ p₁ ih k₂ m₂ p₂
  rw [← eq_iff_iff]
  intro _ _; subst k₁ m₁
  simp [← ih p₂, ← Bool.and'_eq_and]; rfl

abbrev Poly.denote [Ring α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => Int.cast k
  | .add k m p => k • (m.denote ctx) + denote ctx p

abbrev denoteTerm [Ring α] (ctx : Context α) (k : Int) (m : Mon) : α :=
  bif k == 1 then
    m.denote' ctx
  else
    k • m.denote' ctx

abbrev Poly.denote'.go [Ring α] (ctx : Context α) (p : Poly) (acc : α) : α :=
    match p with
    | .num 0 => acc
    | .num k => acc + Int.cast k
    | .add k m p => go ctx p (acc + denoteTerm ctx k m)

abbrev Poly.denote' [Ring α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => Int.cast k
  | .add k m p => denote'.go ctx p (denoteTerm ctx k m)

attribute [semireducible] Poly.denote Poly.denote' Poly.denote'.go denoteTerm

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

noncomputable def Poly.addConst_k (p : Poly) (k : Int) : Poly :=
  Bool.rec
    (Poly.rec (fun k' => .num (Int.add k' k)) (fun k' m _ ih => .add k' m ih) p)
    p
    (Int.beq' k 0)

theorem Poly.addConst_k_eq_addConst (p : Poly) (k : Int) : addConst_k p k = addConst p k := by
  unfold addConst_k addConst; rw [cond_eq_ite]
  split
  next h => rw [← Int.beq'_eq_beq] at h; rw [h]
  next h =>
    rw [← Int.beq'_eq_beq, Bool.not_eq_true] at h; simp [h]
    induction p <;> simp [addConst.go]
    next ih => rw [← ih]

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

noncomputable def Poly.mulConst_k (k : Int) (p : Poly) : Poly :=
  Bool.rec
    (Bool.rec
      (Poly.rec (fun k' => .num (Int.mul k k')) (fun k' m _ ih => .add (Int.mul k k') m ih) p)
      p (Int.beq' k 1))
    (.num 0)
    (Int.beq' k 0)

@[simp] theorem Poly.mulConst_k_eq_mulConst (k : Int) (p : Poly) : p.mulConst_k k = p.mulConst k := by
  simp [mulConst_k, mulConst, cond_eq_ite]; split
  next =>
    have h : Int.beq' k 0 = true := by simp [*]
    simp [h]
  next =>
    have h₁ : Int.beq' k 0 = false := by rw [← Bool.not_eq_true, Int.beq'_eq]; assumption
    split
    next =>
      have h₂ : Int.beq' k 1 = true := by simp [*]
      simp [h₁, h₂]
    next =>
      have h₂ : Int.beq' k 1 = false := by rw [← Bool.not_eq_true, Int.beq'_eq]; assumption
      simp [h₁, h₂]
      induction p
      next => rfl
      next k m p ih => simp [mulConst.go, ← ih]

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

noncomputable def Poly.mulMon_k (k : Int) (m : Mon) (p : Poly) : Poly :=
  Bool.rec
    (Bool.rec
      (Poly.rec
        (fun k' => Bool.rec (.add (Int.mul k k') m (.num 0)) (.num 0) (Int.beq' k' 0))
        (fun k' m' _ ih => .add (Int.mul k k') (m.mul_k m') ih)
        p)
      (p.mulConst_k k)
      (Mon.beq' m .unit))
    (.num 0)
    (Int.beq' k 0)

@[simp] theorem Poly.mulMon_k_eq_mulMon (k : Int) (m : Mon) (p : Poly) : p.mulMon_k k m = p.mulMon k m := by
  simp [mulMon_k, mulMon, cond_eq_ite]; split
  next =>
    have h : Int.beq' k 0 = true := by simp [*]
    simp [h]
  next =>
    have h₁ : Int.beq' k 0 = false := by rw [← Bool.not_eq_true, Int.beq'_eq]; assumption
    simp [h₁]; split
    next h =>
      have h₂ : m.beq' .unit = true := by rw [Mon.beq'_eq]; simp at h; assumption
      simp [h₂]
    next h =>
      have h₂ : m.beq' .unit = false := by rw [← Bool.not_eq_true, Mon.beq'_eq]; simp at h; assumption
      simp [h₂]
      induction p <;> simp [mulMon.go, cond_eq_ite]
      next k =>
        split
        next =>
          have h : Int.beq' k 0 = true := by simp [*]
          simp [h]
        next =>
          have h : Int.beq' k 0 = false := by simp [*]
          simp [h]
      next ih => simp [← ih, Mon.mul_k_eq_mul]

def Poly.mulMon_nc (k : Int) (m : Mon) (p : Poly) : Poly :=
  bif k == 0 then
    .num 0
  else bif m == .unit then
    p.mulConst k
  else
    go p (.num 0)
where
  go (p : Poly) (acc : Poly) : Poly :=
    match p with
    | .num k' => acc.insert (k*k') m
    | .add k' m' p => go p (acc.insert (k*k') (m.mul_nc m'))

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

/-- A `Poly.combine` optimized for the kernel. -/
noncomputable def Poly.combine_k : Poly → Poly → Poly :=
  Nat.rec Poly.concat
    (fun _ ih p₁ =>
      Poly.rec
        (fun k₁ p₂ => Poly.rec
          (fun k₂ => .num (Int.add k₁ k₂))
          (fun k₂ m₂ p₂ _ => addConst_k (.add k₂ m₂ p₂) k₁)
          p₂)
        (fun k₁ m₁ p₁ _ p₂ => Poly.rec
          (fun k₂ => addConst_k (.add k₁ m₁ p₁) k₂)
          (fun k₂ m₂ p₂ _ => Ordering.rec
            (.add k₂ m₂ (ih (.add k₁ m₁ p₁) p₂))
            (let k := Int.add k₁ k₂
             Bool.rec
               (.add k m₁ (ih p₁ p₂))
               (ih p₁ p₂)
               (Int.beq' k 0))
            (.add k₁ m₁ (ih p₁ (.add k₂ m₂ p₂)))
            (m₁.grevlex_k m₂))
          p₂)
        p₁)
    hugeFuel

@[simp] theorem Poly.combine_k_eq_combine (p₁ p₂ : Poly) : p₁.combine_k p₂ = p₁.combine p₂ := by
  unfold Poly.combine Poly.combine_k
  generalize hugeFuel = fuel
  induction fuel generalizing p₁ p₂
  next => simp [Poly.combine.go]; rfl
  next =>
   unfold Poly.combine.go; simp only [Int.add_def]
   split <;> simp only [← addConst_k_eq_addConst, ← Mon.grevlex_k_eq_grevlex]
   next ih _ _ k₁ m₁ p₁ k₂ m₂ p₂ =>
    split
    next h =>
      simp [h, Int.add_def, ← ih p₁ p₂, cond]
      split
      next h => rw [← Int.beq'_eq_beq] at h; simp [h]
      next h => rw [← Int.beq'_eq_beq] at h; simp [h]
    next h => simp [h]; rw [← ih p₁ (add k₂ m₂ p₂)]; rfl
    next h => simp [h]; rw [← ih (add k₁ m₁ p₁) p₂]; rfl

def Poly.mul (p₁ : Poly) (p₂ : Poly) : Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | .num k => acc.combine (p₂.mulConst k)
    | .add k m p₁ => go p₁ (acc.combine (p₂.mulMon k m))

def Poly.mul_nc (p₁ : Poly) (p₂ : Poly) : Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | .num k => acc.combine (p₂.mulConst k)
    | .add k m p₁ => go p₁ (acc.combine (p₂.mulMon_nc k m))

def Poly.pow (p : Poly) (k : Nat) : Poly :=
  match k with
  | 0 => .num 1
  | 1 => p
  | k+1 => p.mul (pow p k)

def Poly.pow_nc (p : Poly) (k : Nat) : Poly :=
  match k with
  | 0 => .num 1
  | 1 => p
  | k+1 => (pow_nc p k).mul_nc p

def Expr.toPoly : Expr → Poly
  | .num k     => .num k
  | .intCast k => .num k
  | .natCast k => .num k
  | .var x     => Poly.ofVar x
  | .add a b   => a.toPoly.combine b.toPoly
  | .mul a b   => a.toPoly.mul b.toPoly
  | .neg a     => a.toPoly.mulConst (-1)
  | .sub a b   => a.toPoly.combine (b.toPoly.mulConst (-1))
  | .pow a k   =>
    bif k == 0 then
      .num 1
    else  match a with
    | .num n => .num (n^k)
    | .intCast n => .num (n^k)
    | .natCast n => .num (n^k)
    | .var x => Poly.ofMon (.mult {x, k} .unit)
    | _ => a.toPoly.pow k

noncomputable def Expr.toPoly_k (e : Expr) : Poly :=
  Expr.rec
    (fun k => .num k) (fun k => .num k) (fun k => .num k)
    (fun x => .ofVar x)
    (fun _ ih => ih.mulConst_k (-1))
    (fun _ _ ih₁ ih₂ => ih₁.combine_k ih₂)
    (fun _ _ ih₁ ih₂ => ih₁.combine_k (ih₂.mulConst_k (-1)))
    (fun _ _ ih₁ ih₂ => ih₁.mul ih₂)
    (fun a k ih => Bool.rec
      (Expr.rec (fun n => .num (n^k)) (fun n => .num (n^k)) (fun n => (.num (n^k)))
        (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => ih.pow k)
        (fun _ _ _ _ => ih.pow k)
        (fun _ _ _ _ => ih.pow k)
        (fun _ _ _ _ => ih.pow k)
        (fun _ _ _ => ih.pow k)
        a)
      (.num 1)
      (k.beq 0))
    e

def Mon.degreeOf (m : Mon) (x : Var) : Nat :=
  match m with
  | .unit => 0
  | .mult pw m => bif pw.x == x then pw.k else degreeOf m x

def Mon.cancelVar (m : Mon) (x : Var) : Mon :=
  match m with
  | .unit => .unit
  | .mult pw m => bif pw.x == x then m else .mult pw (cancelVar m x)

def Poly.cancelVar' (c : Int) (x : Var) (p : Poly) (acc : Poly) : Poly :=
  match p with
  | .num k => acc.addConst k
  | .add k m p =>
    let n := m.degreeOf x
    bif n > 0 && c^n ∣ k then
      cancelVar' c x p (acc.insert (k / (c^n)) (m.cancelVar x))
    else
      cancelVar' c x p (acc.insert k m)

def Poly.cancelVar (c : Int) (x : Var) (p : Poly) : Poly :=
  cancelVar' c x p (.num 0)

@[simp] theorem Expr.toPoly_k_eq_toPoly (e : Expr) : e.toPoly_k = e.toPoly := by
  induction e <;> simp only [toPoly, toPoly_k]
  next a ih => rw [Poly.mulConst_k_eq_mulConst]; congr
  case add => rw [← Poly.combine_k_eq_combine]; congr
  case sub => rw [← Poly.combine_k_eq_combine, ← Poly.mulConst_k_eq_mulConst]; congr
  case mul => congr
  case pow a k ih =>
    rw [cond_eq_ite]; split
    next h => rw [Nat.beq_eq_true_eq, ← Nat.beq_eq] at h; rw [h]
    next h =>
      rw [Nat.beq_eq_true_eq, ← Nat.beq_eq, Bool.not_eq_true] at h; rw [h]; dsimp only
      show
        (Expr.rec (fun n => .num (n^k)) (fun n => .num (n^k)) (fun n => (.num (n^k)))
          (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => a.toPoly_k.pow k)
          (fun _ _ _ _ => a.toPoly_k.pow k)
          (fun _ _ _ _ => a.toPoly_k.pow k)
          (fun _ _ _ _ => a.toPoly_k.pow k)
          (fun _ _ _ => a.toPoly_k.pow k)
          a) = match a with
            | num n => Poly.num (n ^ k)
            | .intCast n => .num (n^k)
            | .natCast n => .num (n^k)
            | var x => Poly.ofMon (Mon.mult { x := x, k := k } Mon.unit)
            | x => a.toPoly.pow k
      cases a <;> try simp [*]

def Expr.toPoly_nc : Expr → Poly
  | .num k     => .num k
  | .intCast k => .num k
  | .natCast k => .num k
  | .var x     => Poly.ofVar x
  | .add a b   => a.toPoly_nc.combine b.toPoly_nc
  | .mul a b   => a.toPoly_nc.mul_nc b.toPoly_nc
  | .neg a     => a.toPoly_nc.mulConst (-1)
  | .sub a b   => a.toPoly_nc.combine (b.toPoly_nc.mulConst (-1))
  | .pow a k   =>
    bif k == 0 then
      .num 1
    else  match a with
    | .num n => .num (n^k)
    | .intCast n => .num (n^k)
    | .natCast n => .num (n^k)
    | .var x => Poly.ofMon (.mult {x, k} .unit)
    | _ => a.toPoly_nc.pow_nc k

def Poly.normEq0 (p : Poly) (c : Nat) : Poly :=
  match p with
  | .num a =>
    bif a % c == 0 then .num 0 else .num a
  | .add a m p =>
    bif a % c == 0 then normEq0 p c else .add a m (.normEq0 p c)

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

def Poly.mulMonC_nc (k : Int) (m : Mon) (p : Poly) (c : Nat) : Poly :=
  let k := k % c
  bif k == 0 then
    .num 0
  else bif m == .unit then
    p.mulConstC k c
  else
    go p (.num 0)
where
  go (p : Poly) (acc : Poly) : Poly :=
    match p with
    | .num k' => acc.insert (k*k' % c) m
    | .add k' m' p => go p (acc.insert (k*k' % c) (m.mul_nc m'))

@[semireducible]
def Poly.combineC (p₁ p₂ : Poly) (c : Nat) : Poly := match p₁, p₂ with
  | .num k₁, .num k₂ => .num ((k₁ + k₂) % c)
  | .num k₁, .add k₂ m₂ p₂ => addConstC (.add k₂ m₂ p₂) k₁ c
  | .add k₁ m₁ p₁, .num k₂ => addConstC (.add k₁ m₁ p₁) k₂ c
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
    match m₁.grevlex m₂ with
    | .eq =>
      let k := (k₁ + k₂) % c
      bif k == 0 then
        combineC p₁ p₂ c
      else
        .add k m₁ (combineC p₁ p₂ c)
    | .gt => .add k₁ m₁ (combineC p₁ (.add k₂ m₂ p₂) c)
    | .lt => .add k₂ m₂ (combineC (.add k₁ m₁ p₁) p₂ c)
termination_by sizeOf p₁ + sizeOf p₂

def Poly.mulC (p₁ : Poly) (p₂ : Poly) (c : Nat) : Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | .num k => acc.combineC (p₂.mulConstC k c) c
    | .add k m p₁ => go p₁ (acc.combineC (p₂.mulMonC k m c) c)

def Poly.mulC_nc (p₁ : Poly) (p₂ : Poly) (c : Nat) : Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | .num k => acc.combineC (p₂.mulConstC k c) c
    | .add k m p₁ => go p₁ (acc.combineC (p₂.mulMonC_nc k m c) c)

def Poly.powC (p : Poly) (k : Nat) (c : Nat) : Poly :=
  match k with
  | 0 => .num 1
  | 1 => p
  | k+1 => p.mulC (powC p k c) c

def Poly.powC_nc (p : Poly) (k : Nat) (c : Nat) : Poly :=
  match k with
  | 0 => .num 1
  | 1 => p
  | k+1 => (powC_nc p k c).mulC_nc p c

def Expr.toPolyC (e : Expr) (c : Nat) : Poly :=
  go e
where
  go : Expr → Poly
    | .num k     => .num (k % c)
    | .natCast k => .num (k % c)
    | .intCast k => .num (k % c)
    | .var x     => Poly.ofVar x
    | .add a b   => (go a).combineC (go b) c
    | .mul a b   => (go a).mulC (go b) c
    | .neg a     => (go a).mulConstC (-1) c
    | .sub a b   => (go a).combineC ((go b).mulConstC (-1) c) c
    | .pow a k   =>
      bif k == 0 then
        .num 1
      else match a with
      | .num n => .num ((n^k) % c)
      | .var x => Poly.ofMon (.mult {x, k} .unit)
      | _ => (go a).powC k c

def Expr.toPolyC_nc (e : Expr) (c : Nat) : Poly :=
  go e
where
  go : Expr → Poly
    | .num k     => .num (k % c)
    | .natCast k => .num (k % c)
    | .intCast k => .num (k % c)
    | .var x     => Poly.ofVar x
    | .add a b   => (go a).combineC (go b) c
    | .mul a b   => (go a).mulC_nc (go b) c
    | .neg a     => (go a).mulConstC (-1) c
    | .sub a b   => (go a).combineC ((go b).mulConstC (-1) c) c
    | .pow a k   =>
      bif k == 0 then
        .num 1
      else match a with
      | .num n => .num ((n^k) % c)
      | .var x => Poly.ofMon (.mult {x, k} .unit)
      | _ => (go a).powC_nc k c

/-!
Theorems for justifying the procedure for commutative rings in `grind`.
-/

open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg
open CommSemiring

theorem denoteInt_eq {α} [Ring α] (k : Int) : denoteInt (α := α) k = k := by
  simp [denoteInt] <;> cases h : k.blt' 0 <;> simp <;> simp at h
  next h => rw [ofNat_eq_natCast, ← intCast_natCast, ← Int.eq_natAbs_of_nonneg h]
  next h => rw [ofNat_eq_natCast, ← intCast_natCast, ← Ring.intCast_neg, ← Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt h)]

theorem Power.denote_eq {α} [Semiring α] (ctx : Context α) (p : Power)
    : p.denote ctx = p.x.denote ctx ^ p.k := by
  cases p <;> simp [Power.denote] <;> split <;> simp [pow_zero, pow_succ, one_mul]

theorem Mon.denote'_eq_denote {α} [Semiring α] (ctx : Context α) (m : Mon) : m.denote' ctx = m.denote ctx := by
  cases m <;> simp [denote', denote]
  rename_i pw m
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

theorem Mon.denote_mulPow_nc {α} [Semiring α] (ctx : Context α) (p : Power) (m : Mon)
    : denote ctx (mulPow_nc p m) = p.denote ctx * m.denote ctx := by
  fun_cases mulPow_nc <;> simp [denote, *]
  next h =>
    simp at h
    simp [Power.denote_eq, pow_add, mul_assoc, h]

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

theorem Mon.denote_mul_nc {α} [Semiring α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (mul_nc m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  fun_induction mul_nc <;> simp [denote, Semiring.one_mul, Semiring.mul_one, denote_mulPow_nc, Semiring.mul_assoc, *]

theorem Var.eq_of_revlex {x₁ x₂ : Var} : x₁.revlex x₂ = .eq → x₁ = x₂ := by
  simp [revlex, cond_eq_ite] <;> split <;> simp
  next h₁ => intro h₂; exact Nat.le_antisymm h₂ (Nat.ge_of_not_lt h₁)

theorem eq_of_powerRevlex {k₁ k₂ : Nat} : powerRevlex k₁ k₂ = .eq → k₁ = k₂ := by
  simp [powerRevlex, cond_eq_ite] <;> split <;> simp
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

theorem Poly.denoteTerm_eq  {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) : denoteTerm ctx k m = k * m.denote ctx := by
  simp [denoteTerm, Mon.denote'_eq_denote, cond_eq_ite, zsmul_eq_intCast_mul]; intro; subst k; rw [Ring.intCast_one, Semiring.one_mul]

theorem Poly.denote'_eq_denote {α} [Ring α] (ctx : Context α) (p : Poly) : p.denote' ctx = p.denote ctx := by
  cases p <;> simp [denote', denote, denoteTerm_eq, zsmul_eq_intCast_mul]
  next k m p =>
    generalize k * m.denote ctx = acc
    fun_induction denote'.go <;> simp [denote, *, Ring.intCast_zero, Semiring.add_zero, denoteTerm_eq]
    next ih => simp [denoteTerm_eq] at ih; simp [ih, Semiring.add_assoc, zsmul_eq_intCast_mul]

theorem Poly.denote_ofMon {α} [Ring α] (ctx : Context α) (m : Mon)
    : denote ctx (ofMon m) = m.denote ctx := by
  simp [ofMon, denote, intCast_one, intCast_zero, one_mul, add_zero, zsmul_eq_intCast_mul]

theorem Poly.denote_ofVar {α} [Ring α] (ctx : Context α) (x : Var)
    : denote ctx (ofVar x) = x.denote ctx := by
  simp [ofVar, denote_ofMon, Mon.denote_ofVar]

theorem Poly.denote_addConst {α} [Ring α] (ctx : Context α) (p : Poly) (k : Int) : (addConst p k).denote ctx = p.denote ctx + k := by
  simp [addConst, cond_eq_ite]; split
  next => simp [*, intCast_zero, add_zero]
  next =>
    fun_induction addConst.go <;> simp [denote, *]
    next => rw [intCast_add]
    next => simp [add_comm, add_left_comm]

theorem Poly.denote_insert {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (insert k m p).denote ctx = k * m.denote ctx + p.denote ctx := by
  simp [insert, cond_eq_ite] <;> split
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

theorem Poly.denote_concat {α} [Ring α] (ctx : Context α) (p₁ p₂ : Poly)
    : (concat p₁ p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  fun_induction concat <;> simp [*, denote_addConst, denote]
  next => rw [add_comm]
  next => rw [add_assoc]

theorem Poly.denote_mulConst {α} [Ring α] (ctx : Context α) (k : Int) (p : Poly)
    : (mulConst k p).denote ctx = k * p.denote ctx := by
  simp [mulConst, cond_eq_ite] <;> split
  next => simp [denote, *, intCast_zero, zero_mul]
  next =>
    split <;> try simp [*, intCast_one, one_mul]
    fun_induction mulConst.go <;> simp [denote, *]
    next => rw [intCast_mul]
    next => rw [left_distrib, ← zsmul_eq_intCast_mul, ← zsmul_eq_intCast_mul, mul_zsmul]

theorem Poly.denote_mulMon {α} [CommRing α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (mulMon k m p).denote ctx = k * m.denote ctx * p.denote ctx := by
  simp [mulMon, cond_eq_ite] <;> split
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

theorem Poly.denote_mulMon_nc_go {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) (p acc : Poly)
    : (mulMon_nc.go k m p acc).denote ctx = k * m.denote ctx * p.denote ctx + acc.denote ctx := by
  fun_induction mulMon_nc.go <;> simp [denote, denote_insert, zsmul_eq_intCast_mul]
  next => rw [Ring.intCast_mul, Semiring.mul_assoc, Semiring.mul_assoc, ← Ring.intCast_mul_comm]
  next ih =>
    rw [ih, denote_insert, Mon.denote_mul_nc, Semiring.left_distrib, Ring.intCast_mul]
    rw [Ring.intCast_mul_left_comm]; simp [← Semiring.mul_assoc]
    conv => enter [1, 2, 1, 1, 1]; rw [Ring.intCast_mul_comm]
    simp [Semiring.add_assoc, Semiring.add_comm, add_left_comm]

theorem Poly.denote_mulMon_nc {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (mulMon_nc k m p).denote ctx = k * m.denote ctx * p.denote ctx := by
  simp [mulMon_nc, cond_eq_ite] <;> split
  next => simp [denote, *, intCast_zero, zero_mul]
  next =>
    split
    next h =>
      simp at h; simp [*, Mon.denote, mul_one, denote_mulConst]
    next =>
      rw [denote_mulMon_nc_go]; simp [denote, Ring.intCast_zero, add_zero]

theorem Poly.denote_combine {α} [Ring α] (ctx : Context α) (p₁ p₂ : Poly)
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

theorem Poly.denote_mul_nc_go {α} [Ring α] (ctx : Context α) (p₁ p₂ acc : Poly)
    : (mul_nc.go p₂ p₁ acc).denote ctx = acc.denote ctx + p₁.denote ctx * p₂.denote ctx := by
  fun_induction mul_nc.go
    <;> simp [denote_combine, denote_mulConst, denote, *, right_distrib, denote_mulMon_nc, add_assoc, zsmul_eq_intCast_mul]

theorem Poly.denote_mul_nc {α} [Ring α] (ctx : Context α) (p₁ p₂ : Poly)
    : (mul_nc p₁ p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  simp [mul_nc, denote_mul_nc_go, denote, intCast_zero, zero_add]

theorem Poly.denote_pow {α} [CommRing α] (ctx : Context α) (p : Poly) (k : Nat)
   : (pow p k).denote ctx = p.denote ctx ^ k := by
 fun_induction pow
 next => simp [denote, intCast_one, pow_zero]
 next => simp [pow_succ, pow_zero, one_mul]
 next => simp [denote_mul, *, pow_succ, mul_comm]

theorem Poly.denote_pow_nc {α} [Ring α] (ctx : Context α) (p : Poly) (k : Nat)
   : (pow_nc p k).denote ctx = p.denote ctx ^ k := by
 fun_induction pow_nc
 next => simp [denote, intCast_one, pow_zero]
 next => simp [pow_succ, pow_zero, one_mul]
 next => simp [denote_mul_nc, *, pow_succ]

theorem Expr.denote_toPoly {α} [CommRing α] (ctx : Context α) (e : Expr)
   : e.toPoly.denote ctx = e.denote ctx := by
  fun_induction toPoly
    <;> simp [denote, Poly.denote, Poly.denote_ofVar, Poly.denote_combine,
          Poly.denote_mul, Poly.denote_mulConst, Poly.denote_pow, intCast_pow, intCast_neg, intCast_one,
          neg_mul, one_mul, sub_eq_add_neg, denoteInt_eq, *]
  next => rw [Ring.intCast_natCast]
  next a k h => simp at h; simp [h, Semiring.pow_zero]
  next => rw [Ring.intCast_natCast]
  next => simp [Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one]

theorem Expr.denote_toPoly_nc {α} [Ring α] (ctx : Context α) (e : Expr)
   : e.toPoly_nc.denote ctx = e.denote ctx := by
  fun_induction toPoly_nc
    <;> simp [denote, Poly.denote, Poly.denote_ofVar, Poly.denote_combine,
          Poly.denote_mul_nc, Poly.denote_mulConst, Poly.denote_pow_nc, intCast_pow, intCast_neg, intCast_one,
          neg_mul, one_mul, sub_eq_add_neg, denoteInt_eq, *]
  next => rw [Ring.intCast_natCast]
  next a k h => simp at h; simp [h, Semiring.pow_zero]
  next => rw [Ring.intCast_natCast]
  next => simp [Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one]

theorem Expr.eq_of_toPoly_eq {α} [CommRing α] (ctx : Context α) (a b : Expr) (h : a.toPoly == b.toPoly) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [denote_toPoly] at h
  assumption

theorem Expr.eq_of_toPoly_nc_eq {α} [Ring α] (ctx : Context α) (a b : Expr) (h : a.toPoly_nc == b.toPoly_nc) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [denote_toPoly_nc] at h
  assumption

section
attribute [local simp] Semiring.pow_zero Semiring.mul_one Semiring.one_mul cond_eq_ite

theorem Mon.denote_cancelVar [CommSemiring α] (ctx : Context α) (m : Mon) (x : Var)
    : m.denote ctx = x.denote ctx ^ (m.degreeOf x) * (m.cancelVar x).denote ctx := by
  fun_induction cancelVar <;> simp [degreeOf]
  next h =>
    simp at h; simp [*, denote, Power.denote_eq]
  next h ih =>
    simp at h; simp [*, denote, Semiring.mul_assoc, CommSemiring.mul_comm, CommSemiring.mul_left_comm]

theorem Poly.denote_cancelVar' {α} [CommRing α] (ctx : Context α) (p : Poly) (c : Int) (x : Var) (acc : Poly)
    : c ≠ 0 → c * x.denote ctx = 1 → (p.cancelVar' c x acc).denote ctx = p.denote ctx + acc.denote ctx := by
  intro h₁ h₂
  fun_induction cancelVar'
  next acc k => simp [denote_addConst, denote, Semiring.add_comm]
  next h ih =>
    simp [ih, denote_insert, denote]
    conv => rhs; rw [Mon.denote_cancelVar (x := x)]
    simp [← Semiring.add_assoc]
    congr 1
    rw [Semiring.add_comm, Ring.zsmul_eq_intCast_mul,]
    congr 1
    simp +zetaDelta [Int.dvd_def] at h
    have ⟨d, h⟩ := h.2
    simp +zetaDelta [h]
    rw [Int.mul_ediv_cancel_left _ (Int.pow_ne_zero h₁)]
    rw [Ring.intCast_mul]
    conv => rhs; lhs; rw [CommSemiring.mul_comm]
    rw [Semiring.mul_assoc, Ring.intCast_pow]
    congr 1
    rw [← Semiring.mul_assoc, ← CommSemiring.mul_pow, h₂, Semiring.one_pow, Semiring.one_mul]
  next ih =>
    simp [ih, denote_insert, denote, Ring.zsmul_eq_intCast_mul, Semiring.add_assoc,
      Semiring.add_comm, add_left_comm]

theorem Poly.denote_cancelVar {α} [CommRing α] (ctx : Context α) (p : Poly) (c : Int) (x : Var)
    : c ≠ 0 → c * x.denote ctx = 1 → (p.cancelVar c x).denote ctx = p.denote ctx := by
  intro h₁ h₂
  have := denote_cancelVar' ctx p c x (.num 0) h₁ h₂
  rw [cancelVar, this, denote, Ring.intCast_zero, Semiring.add_zero]

noncomputable def cancel_var_cert (c : Int) (x : Var) (p₁ p₂ : Poly) : Bool :=
  c != 0 && p₂.beq' (p₁.cancelVar c x)

theorem eq_cancel_var {α} [CommRing α] (ctx : Context α) (c : Int) (x : Var) (p₁ p₂ : Poly)
    : cancel_var_cert c x p₁ p₂ → c * x.denote ctx = 1 → p₁.denote ctx = 0 → p₂.denote ctx = 0 := by
  simp [cancel_var_cert]; intros h₁ _ h₂ _; subst p₂
  simp [Poly.denote_cancelVar ctx p₁ c x h₁ h₂]; assumption

theorem diseq_cancel_var {α} [CommRing α] (ctx : Context α) (c : Int) (x : Var) (p₁ p₂ : Poly)
    : cancel_var_cert c x p₁ p₂ → c * x.denote ctx = 1 → p₁.denote ctx ≠ 0 → p₂.denote ctx ≠ 0 := by
  simp [cancel_var_cert]; intros h₁ _ h₂ _; subst p₂
  simp [Poly.denote_cancelVar ctx p₁ c x h₁ h₂]; assumption

theorem le_cancel_var {α} [CommRing α] [LE α] (ctx : Context α) (c : Int) (x : Var) (p₁ p₂ : Poly)
    : cancel_var_cert c x p₁ p₂ → c * x.denote ctx = 1 → p₁.denote ctx ≤ 0 → p₂.denote ctx ≤ 0 := by
  simp [cancel_var_cert]; intros h₁ _ h₂ _; subst p₂
  simp [Poly.denote_cancelVar ctx p₁ c x h₁ h₂]; assumption

theorem lt_cancel_var {α} [CommRing α] [LT α] (ctx : Context α) (c : Int) (x : Var) (p₁ p₂ : Poly)
    : cancel_var_cert c x p₁ p₂ → c * x.denote ctx = 1 → p₁.denote ctx < 0 → p₂.denote ctx < 0 := by
  simp [cancel_var_cert]; intros h₁ _ h₂ _; subst p₂
  simp [Poly.denote_cancelVar ctx p₁ c x h₁ h₂]; assumption

end
/-!
Theorems for justifying the procedure for commutative rings with a characteristic in `grind`.
-/

theorem Poly.denote_addConstC {α c} [Ring α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Int) : (addConstC p k c).denote ctx = p.denote ctx + k := by
  fun_induction addConstC <;> simp [denote, *]
  next => rw [IsCharP.intCast_emod, intCast_add]
  next => simp [add_comm, add_left_comm]

theorem Poly.denote_insertC {α c} [Ring α] [IsCharP α c] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (insertC k m p c).denote ctx = k * m.denote ctx + p.denote ctx := by
  simp [insertC, cond_eq_ite] <;> split
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

theorem Poly.denote_mulConstC {α c} [Ring α] [IsCharP α c] (ctx : Context α) (k : Int) (p : Poly)
    : (mulConstC k p c).denote ctx = k * p.denote ctx := by
  simp [mulConstC, cond_eq_ite] <;> split
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
  simp [mulMonC, cond_eq_ite] <;> split
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

theorem Poly.denote_mulMonC_nc_go {α c} [Ring α] [IsCharP α c] (ctx : Context α) (k : Int) (m : Mon) (p acc : Poly)
    : (mulMonC_nc.go k m c p acc).denote ctx = k * m.denote ctx * p.denote ctx + acc.denote ctx := by
  fun_induction mulMonC_nc.go <;> simp [denote, denote_insert, zsmul_eq_intCast_mul]
  next => rw [IsCharP.intCast_emod (x := k * _) (p := c), Ring.intCast_mul, Semiring.mul_assoc, Semiring.mul_assoc, ← Ring.intCast_mul_comm]
  next ih =>
    rw [ih, denote_insert, Mon.denote_mul_nc, IsCharP.intCast_emod (x := k * _) (p := c),
        Semiring.left_distrib, Ring.intCast_mul]
    rw [Ring.intCast_mul_left_comm]; simp [← Semiring.mul_assoc]
    conv => enter [1, 2, 1, 1, 1]; rw [Ring.intCast_mul_comm]
    simp [Semiring.add_assoc, Semiring.add_comm, add_left_comm]

theorem Poly.denote_mulMonC_nc {α c} [Ring α] [IsCharP α c] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (mulMonC_nc k m p c).denote ctx = k * m.denote ctx * p.denote ctx := by
  simp [mulMonC_nc, cond_eq_ite] <;> split
  next =>
    rw [← IsCharP.intCast_emod (p := c)]
    simp [denote, *, intCast_zero, zero_mul]
  next =>
    split
    next h => simp at h; simp [*, Mon.denote, mul_one, denote_mulConstC, IsCharP.intCast_emod]
    next => rw [Poly.denote_mulMonC_nc_go, denote, Ring.intCast_zero, add_zero]

theorem Poly.denote_combineC {α c} [Ring α] [IsCharP α c] (ctx : Context α) (p₁ p₂ : Poly)
    : (combineC p₁ p₂ c).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  fun_induction combineC
    <;> simp [*, denote_addConstC, denote, intCast_add, add_comm, add_left_comm, add_assoc,
      IsCharP.intCast_emod, zsmul_eq_intCast_mul]
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

theorem Poly.denote_mulC_nc_go {α c} [Ring α] [IsCharP α c] (ctx : Context α) (p₁ p₂ acc : Poly)
    : (mulC_nc.go p₂ c p₁ acc).denote ctx = acc.denote ctx + p₁.denote ctx * p₂.denote ctx := by
  fun_induction mulC_nc.go
    <;> simp [denote_combineC, denote_mulConstC, denote, *, right_distrib, denote_mulMonC_nc, add_assoc, zsmul_eq_intCast_mul]

theorem Poly.denote_mulC_nc {α c} [Ring α] [IsCharP α c] (ctx : Context α) (p₁ p₂ : Poly)
    : (mulC_nc p₁ p₂ c).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  simp [mulC_nc, denote_mulC_nc_go, denote, intCast_zero, zero_add]

theorem Poly.denote_powC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Nat)
   : (powC p k c).denote ctx = p.denote ctx ^ k := by
 fun_induction powC
 next => simp [denote, intCast_one, pow_zero]
 next => simp [pow_succ, pow_zero, one_mul]
 next => simp [denote_mulC, *, pow_succ, mul_comm]

theorem Poly.denote_powC_nc {α c} [Ring α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Nat)
   : (powC_nc p k c).denote ctx = p.denote ctx ^ k := by
 fun_induction powC_nc
 next => simp [denote, intCast_one, pow_zero]
 next => simp [pow_succ, pow_zero, one_mul]
 next => simp [denote_mulC_nc, *, pow_succ]

theorem Expr.denote_toPolyC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (e : Expr)
   : (e.toPolyC c).denote ctx = e.denote ctx := by
  unfold toPolyC
  fun_induction toPolyC.go
    <;> simp [denote, Poly.denote, Poly.denote_ofVar, Poly.denote_combineC,
          Poly.denote_mulC, Poly.denote_mulConstC, Poly.denote_powC, denoteInt_eq, *]
  next => rw [IsCharP.intCast_emod]
  next => rw [IsCharP.intCast_emod, Ring.intCast_natCast]
  next => rw [IsCharP.intCast_emod]
  next => rw [intCast_neg, neg_mul, intCast_one, one_mul]
  next => rw [intCast_neg, neg_mul, intCast_one, one_mul, sub_eq_add_neg]
  next a k h => simp at h; simp [h, Semiring.pow_zero, Ring.intCast_one]
  next => rw [IsCharP.intCast_emod, intCast_pow]
  next => simp [Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one]

theorem Expr.denote_toPolyC_nc {α c} [Ring α] [IsCharP α c] (ctx : Context α) (e : Expr)
   : (e.toPolyC_nc c).denote ctx = e.denote ctx := by
  unfold toPolyC_nc
  fun_induction toPolyC_nc.go
    <;> simp [denote, Poly.denote, Poly.denote_ofVar, Poly.denote_combineC,
          Poly.denote_mulC_nc, Poly.denote_mulConstC, Poly.denote_powC_nc, denoteInt_eq, *]
  next => rw [IsCharP.intCast_emod]
  next => rw [IsCharP.intCast_emod, Ring.intCast_natCast]
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

theorem Expr.eq_of_toPolyC_nc_eq {α c} [Ring α] [IsCharP α c] (ctx : Context α) (a b : Expr)
    (h : a.toPolyC_nc c == b.toPolyC_nc c) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [denote_toPolyC_nc] at h
  assumption

namespace Stepwise
/-!
Theorems for stepwise proof-term construction
-/
noncomputable def core_cert (lhs rhs : Expr) (p : Poly) : Bool :=
  (lhs.sub rhs).toPoly_k.beq' p

theorem core {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  simp [core_cert]; intro; subst p
  simp [Expr.denote_toPoly, Expr.denote]
  simp [sub_eq_zero_iff]

noncomputable def superpose_cert (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) : Bool :=
  (p₁.mulMon_k k₁ m₁).combine_k (p₂.mulMon_k k₂ m₂) |>.beq' p

theorem superpose {α} [CommRing α] (ctx : Context α) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : superpose_cert k₁ m₁ p₁ k₂ m₂ p₂ p → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [superpose_cert]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combine, Poly.denote_mulMon, h₁, h₂, mul_zero, add_zero]

noncomputable def simp_cert (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) : Bool :=
  (p₁.mulConst_k k₁).combine_k (p₂.mulMon_k k₂ m₂) |>.beq' p

theorem simp {α} [CommRing α] (ctx : Context α) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : simp_cert k₁ p₁ k₂ m₂ p₂ p → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [simp_cert]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combine, Poly.denote_mulMon, Poly.denote_mulConst, h₁, h₂, mul_zero, add_zero]

noncomputable def mul_cert (p₁ : Poly) (k : Int) (p : Poly) : Bool :=
  p₁.mulConst_k k |>.beq' p

theorem mul {α} [CommRing α] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_cert p₁ k p → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [mul_cert]; intro _ h; subst p
  simp [Poly.denote_mulConst, *, mul_zero]

theorem eq_mul {α} [CommRing α] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_cert p₁ k p → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  apply mul

noncomputable def mul_ne_cert (p₁ : Poly) (k : Int) (p : Poly) : Bool :=
  k != 0 && (p₁.mulConst_k k |>.beq' p)

theorem diseq_mul {α} [CommRing α] [NoNatZeroDivisors α] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_ne_cert p₁ k p → p₁.denote ctx ≠ 0 → p.denote ctx ≠ 0 := by
  simp [mul_ne_cert]; intro h₁ _ h₂; subst p
  simp [Poly.denote_mulConst]; intro h₃
  rw [← zsmul_eq_intCast_mul] at h₃
  have := no_int_zero_divisors h₁ h₃
  contradiction

theorem inv {α} [CommRing α] (ctx : Context α) (p₁ : Poly) (p : Poly)
    : mul_cert p₁ (-1) p → p₁.denote ctx = 0 → p.denote ctx = 0 :=
  mul ctx p₁ (-1) p

noncomputable def div_cert (p₁ : Poly) (k : Int) (p : Poly) : Bool :=
  !Int.beq' k 0 |>.and' (p.mulConst_k k |>.beq' p₁)

theorem div {α} [CommRing α] (ctx : Context α) [NoNatZeroDivisors α] (p₁ : Poly) (k : Int) (p : Poly)
    : div_cert p₁ k p → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [div_cert]; intro hnz _ h; subst p₁
  simp [Poly.denote_mulConst, ← zsmul_eq_intCast_mul] at h
  exact no_int_zero_divisors hnz h

noncomputable def unsat_eq_cert (p : Poly) (k : Int) : Bool :=
  !Int.beq' k 0 |>.and' (p.beq' (.num k))

def unsat_eq {α} [CommRing α] (ctx : Context α) [IsCharP α 0] (p : Poly) (k : Int)
    : unsat_eq_cert p k → p.denote ctx = 0 → False := by
  simp [unsat_eq_cert]; intro h _; subst p; simp [Poly.denote]
  have := IsCharP.intCast_eq_zero_iff (α := α) 0 k
  simp [h] at this
  assumption

theorem d_init {α} [CommRing α] (ctx : Context α) (p : Poly) : (1:Int) * p.denote ctx = p.denote ctx := by
  rw [intCast_one, one_mul]

noncomputable def d_step1_cert (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) : Bool :=
  p.beq' (p₁.combine_k (p₂.mulMon_k k₂ m₂))

theorem d_step1 {α} [CommRing α] (ctx : Context α) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : d_step1_cert p₁ k₂ m₂ p₂ p → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  simp [d_step1_cert]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combine, Poly.denote_mulMon, h₂, mul_zero, add_zero, h₁]

noncomputable def d_stepk_cert (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) : Bool :=
  p.beq' ((p₁.mulConst_k k₁).combine_k (p₂.mulMon_k k₂ m₂))

theorem d_stepk {α} [CommRing α] (ctx : Context α) (k₁ : Int) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : d_stepk_cert k₁ p₁ k₂ m₂ p₂ p → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → (k₁*k : Int) * init.denote ctx = p.denote ctx := by
  simp [d_stepk_cert]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combine, Poly.denote_mulMon, Poly.denote_mulConst, h₂, mul_zero, add_zero]
  rw [intCast_mul, mul_assoc, h₁]

noncomputable def imp_1eq_cert (lhs rhs : Expr) (p₁ p₂ : Poly) : Bool :=
  (lhs.sub rhs).toPoly_k.beq' p₁ |>.and' (p₂.beq' (.num 0))

theorem imp_1eq {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_1eq_cert lhs rhs p₁ p₂ → (1:Int) * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_1eq_cert, intCast_one, one_mul]; intro _ _; subst p₁ p₂
  simp [Expr.denote_toPoly, Expr.denote, sub_eq_zero_iff, Poly.denote, intCast_zero]

noncomputable def imp_keq_cert (lhs rhs : Expr) (k : Int) (p₁ p₂ : Poly) : Bool :=
  !Int.beq' k 0 |>.and' ((lhs.sub rhs).toPoly_k.beq' p₁ |>.and' (p₂.beq' (.num 0)))

theorem imp_keq  {α} [CommRing α] (ctx : Context α) [NoNatZeroDivisors α] (k : Int) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_keq_cert lhs rhs k p₁ p₂ → k * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_keq_cert]; intro hnz _ _; subst p₁ p₂
  simp [Expr.denote_toPoly, Expr.denote, Poly.denote, intCast_zero, ← zsmul_eq_intCast_mul]
  intro h; replace h := no_int_zero_divisors hnz h
  rw [← sub_eq_zero_iff, h]

noncomputable def core_certC (lhs rhs : Expr) (p : Poly) (c : Nat) : Bool :=
  (lhs.sub rhs).toPolyC c |>.beq' p

theorem coreC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_certC lhs rhs p c → lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  simp [core_certC]; intro; subst p
  simp [Expr.denote_toPolyC, Expr.denote]
  simp [sub_eq_zero_iff]

noncomputable def superpose_certC (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (c : Nat) : Bool :=
  (p₁.mulMonC k₁ m₁ c).combineC (p₂.mulMonC k₂ m₂ c) c |>.beq' p

theorem superposeC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : superpose_certC k₁ m₁ p₁ k₂ m₂ p₂ p c → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [superpose_certC]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combineC, Poly.denote_mulMonC, h₁, h₂, mul_zero, add_zero]

noncomputable def mul_certC (p₁ : Poly) (k : Int) (p : Poly) (c : Nat) : Bool :=
  p₁.mulConstC k c |>.beq' p

def mulC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_certC p₁ k p c → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [mul_certC]; intro _ h; subst p
  simp [Poly.denote_mulConstC, *, mul_zero]

noncomputable def div_certC (p₁ : Poly) (k : Int) (p : Poly) (c : Nat) : Bool :=
  !Int.beq' k 0 |>.and' ((p.mulConstC k c).beq' p₁)

def divC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) [NoNatZeroDivisors α] (p₁ : Poly) (k : Int) (p : Poly)
    : div_certC p₁ k p c → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [div_certC]; intro hnz _ h; subst p₁
  simp [Poly.denote_mulConstC, ← zsmul_eq_intCast_mul] at h
  exact no_int_zero_divisors hnz h

noncomputable def simp_certC (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (c : Nat) : Bool :=
  (p₁.mulConstC k₁ c).combineC (p₂.mulMonC k₂ m₂ c) c |>.beq' p

theorem simpC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : simp_certC k₁ p₁ k₂ m₂ p₂ p c → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  simp [simp_certC]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combineC, Poly.denote_mulMonC, Poly.denote_mulConstC, h₁, h₂, mul_zero, add_zero]

noncomputable def unsat_eq_certC (p : Poly) (k : Int) (c : Nat) : Bool :=
  !Int.beq' (k % c) 0 |>.and' (p.beq' (.num k))

def unsat_eqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Int)
    : unsat_eq_certC p k c → p.denote ctx = 0 → False := by
  simp [unsat_eq_certC]; intro h _; subst p; simp [Poly.denote]
  have := IsCharP.intCast_eq_zero_iff (α := α) c k
  simp [h] at this
  assumption

noncomputable def d_step1_certC (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (c : Nat) : Bool :=
  p.beq' (p₁.combineC (p₂.mulMonC k₂ m₂ c) c)

theorem d_step1C {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : d_step1_certC p₁ k₂ m₂ p₂ p c → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  simp [d_step1_certC]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combineC, Poly.denote_mulMonC, h₂, mul_zero, add_zero, h₁]

noncomputable def d_stepk_certC (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (c : Nat) : Bool :=
  p.beq' ((p₁.mulConstC k₁ c).combineC (p₂.mulMonC k₂ m₂ c) c)

theorem d_stepkC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly)
    : d_stepk_certC k₁ p₁ k₂ m₂ p₂ p c → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → (k₁*k : Int) * init.denote ctx = p.denote ctx := by
  simp [d_stepk_certC]; intro _ h₁ h₂; subst p
  simp [Poly.denote_combineC, Poly.denote_mulMonC, Poly.denote_mulConstC, h₂, mul_zero, add_zero]
  rw [intCast_mul, mul_assoc, h₁]

noncomputable def imp_1eq_certC (lhs rhs : Expr) (p₁ p₂ : Poly) (c : Nat) : Bool :=
  ((lhs.sub rhs).toPolyC c).beq' p₁ |>.and' (p₂.beq' (.num 0))

theorem imp_1eqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_1eq_certC lhs rhs p₁ p₂ c → (1:Int) * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_1eq_certC, intCast_one, one_mul]; intro _ _; subst p₁ p₂
  simp [Expr.denote_toPolyC, Expr.denote, sub_eq_zero_iff, Poly.denote, intCast_zero]

noncomputable def imp_keq_certC (lhs rhs : Expr) (k : Int) (p₁ p₂ : Poly) (c : Nat) : Bool :=
  !Int.beq' k 0 |>.and' (((lhs.sub rhs).toPolyC c).beq' p₁ |>.and' (p₂.beq' (.num 0)))

theorem imp_keqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) [NoNatZeroDivisors α] (k : Int) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_keq_certC lhs rhs k p₁ p₂ c → k * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_keq_certC]; intro hnz _ _; subst p₁ p₂
  simp [Expr.denote_toPolyC, Expr.denote, Poly.denote, intCast_zero, ← zsmul_eq_intCast_mul]
  intro h; replace h := no_int_zero_divisors hnz h
  rw [← sub_eq_zero_iff, h]

end Stepwise

/-! IntModule interface -/

def Mon.denoteAsIntModule [CommRing α] (ctx : Context α) (m : Mon) : α :=
  match m with
  | .unit => One.one
  | .mult pw m => go m (pw.denote ctx)
where
  go (m : Mon) (acc : α) : α :=
    match m with
    | .unit => acc
    | .mult pw m => go m (acc * pw.denote ctx)

def Poly.denoteAsIntModule [CommRing α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => k • (One.one : α)
  | .add k m p => k • (m.denoteAsIntModule ctx) + denoteAsIntModule ctx p

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
    : core_cert lhs rhs p → lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  apply core

theorem eq_int_module {α} [CommRing α] (ctx : Context α) (p : Poly)
    : p.denote ctx = 0 → p.denoteAsIntModule ctx = 0 := by
  simp [Poly.denoteAsIntModule_eq_denote]

theorem diseq_norm {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx ≠ rhs.denote ctx → p.denote ctx ≠ 0 := by
  simp [core_cert]; intro _ h; subst p; simp [Expr.denote_toPoly, Expr.denote]
  intro h; rw [sub_eq_zero_iff] at h; contradiction

theorem diseq_int_module {α} [CommRing α] (ctx : Context α) (p : Poly)
    : p.denote ctx ≠ 0 → p.denoteAsIntModule ctx ≠ 0 := by
  simp [Poly.denoteAsIntModule_eq_denote]

open OrderedAdd

theorem le_norm {α} [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx ≤ rhs.denote ctx → p.denote ctx ≤ 0 := by
  simp [core_cert]; intro _ h; subst p; simp [Expr.denote_toPoly, Expr.denote]
  replace h := add_le_left h ((-1) * rhs.denote ctx)
  rw [neg_mul, ← sub_eq_add_neg, one_mul, ← sub_eq_add_neg, sub_self] at h
  assumption

theorem le_int_module {α} [CommRing α] [LE α] (ctx : Context α) (p : Poly)
    : p.denote ctx ≤ 0 → p.denoteAsIntModule ctx ≤ 0 := by
  simp [Poly.denoteAsIntModule_eq_denote]

noncomputable def mul_ineq_cert (p₁ : Poly) (k : Int) (p : Poly) : Bool :=
  k > 0 && (p₁.mulConst_k k |>.beq' p)

theorem le_mul {α} [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_ineq_cert p₁ k p → p₁.denote ctx ≤ 0 → p.denote ctx ≤ 0 := by
  simp [mul_ineq_cert]; intro h₁ _ h₂; subst p; simp [Poly.denote_mulConst]
  replace h₂ := zsmul_nonpos (Int.le_of_lt h₁) h₂
  simp [Ring.zsmul_eq_intCast_mul] at h₂
  assumption

theorem lt_norm {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert lhs rhs p → lhs.denote ctx < rhs.denote ctx → p.denote ctx < 0 := by
  simp [core_cert]; intro _ h; subst p; simp [Expr.denote_toPoly, Expr.denote]
  replace h := add_lt_left h ((-1) * rhs.denote ctx)
  rw [neg_mul, ← sub_eq_add_neg, one_mul, ← sub_eq_add_neg, sub_self] at h
  assumption

theorem lt_int_module {α} [CommRing α] [LT α] (ctx : Context α) (p : Poly)
    : p.denote ctx < 0 → p.denoteAsIntModule ctx < 0 := by
  simp [Poly.denoteAsIntModule_eq_denote]

theorem lt_mul {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_ineq_cert p₁ k p → p₁.denote ctx < 0 → p.denote ctx < 0 := by
  simp [mul_ineq_cert]; intro h₁ _ h₂; subst p; simp [Poly.denote_mulConst]
  replace h₂ := zsmul_neg_iff k h₂ |>.mpr h₁
  simp [Ring.zsmul_eq_intCast_mul] at h₂
  assumption

theorem not_le_norm {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert rhs lhs p → ¬ lhs.denote ctx ≤ rhs.denote ctx → p.denote ctx < 0 := by
  simp [core_cert]; intro _ h₁; subst p; simp [Expr.denote_toPoly, Expr.denote]
  replace h₁ := LinearOrder.lt_of_not_le h₁
  replace h₁ := add_lt_left h₁ (-lhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem not_lt_norm {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : core_cert rhs lhs p → ¬ lhs.denote ctx < rhs.denote ctx → p.denote ctx ≤ 0 := by
  simp [core_cert]; intro _ h₁; subst p; simp [Expr.denote_toPoly, Expr.denote]
  replace h₁ := LinearOrder.le_of_not_lt h₁
  replace h₁ := add_le_left h₁ (-lhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem inv_int_eq [Field α] [IsCharP α 0] (b : Int) : b != 0 → (denoteInt b : α) * (denoteInt b)⁻¹ = 1 := by
  simp; intro h
  have : (denoteInt b : α) ≠ 0 := by
    simp [denoteInt_eq]; intro h
    have := IsCharP.intCast_eq_zero_iff (α := α) 0 b; simp [*] at this
  rw [Field.mul_inv_cancel this]

theorem intCast_eq_denoteInt [Field α] (b : Int) : (IntCast.intCast b : α) = denoteInt b := by
  simp [denoteInt_eq]

theorem inv_int_eq' [Field α] [IsCharP α 0] (b : Int) : b != 0 → (IntCast.intCast b : α) * (denoteInt b)⁻¹ = 1 := by
  rw [intCast_eq_denoteInt]
  apply inv_int_eq

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

noncomputable def one_eq_zero_unsat_cert (p : Poly) :=
  p.beq' (.num 1) || p.beq' (.num (-1))

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
  have := Int.mul_ediv_add_emod a ↑c
  rw [h', Int.add_zero] at this
  replace this := congrArg (Int.cast (R := α)) this
  rw [Ring.intCast_mul] at this
  rw [← Ring.intCast_ofNat] at h
  rw [h, Ring.intCast_zero, Semiring.zero_mul] at this
  rw [this]

theorem Poly.normEq0_eq {α} [CommRing α] (ctx : Context α) (p : Poly) (c : Nat) (h : Int.cast c = (0 : α)) : (p.normEq0 c).denote ctx = p.denote ctx := by
  induction p
  next a =>
    simp [denote, normEq0, cond_eq_ite]; split <;> simp [denote]
    next h' => rw [of_mod_eq_0 h h', Ring.intCast_zero]
  next a m p ih =>
    simp [denote, normEq0, cond_eq_ite]; split <;> simp [denote, zsmul_eq_intCast_mul, *]
    next h' => rw [of_mod_eq_0 h h', Semiring.zero_mul, zero_add]

noncomputable def eq_normEq0_cert (c : Nat) (p₁ p₂ p : Poly) : Bool :=
  p₁.beq' (.num c) && (p.beq' (p₂.normEq0 c))

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
  rename_i n m g
  apply gcd_eq_0 g n m a b

noncomputable def d_normEq0_cert (c : Nat) (p₁ p₂ p : Poly) : Bool :=
  p₂.beq' (.num c) |>.and' (p.beq' (p₁.normEq0 c))

theorem d_normEq0 {α} [CommRing α] (ctx : Context α) (k : Int) (c : Nat) (init : Poly) (p₁ p₂ p : Poly)
    : d_normEq0_cert c p₁ p₂ p → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  simp [d_normEq0_cert]; intro _ h₁ h₂; subst p p₂; simp [Poly.denote]
  intro h; rw [p₁.normEq0_eq] <;> assumption

noncomputable def norm_int_cert (e : Expr) (p : Poly) : Bool :=
  e.toPoly_k.beq' p

theorem norm_int (ctx : Context Int) (e : Expr) (p : Poly) : norm_int_cert e p → e.denote ctx = p.denote' ctx := by
  simp [norm_int_cert, Poly.denote'_eq_denote]; intro; subst p; simp [Expr.denote_toPoly]

/-!
Helper theorems for normalizing ring constraints in the `grind order` module.
-/

noncomputable def norm_cnstr_cert (lhs rhs lhs' rhs' : Expr) : Bool :=
  (rhs.sub lhs).toPoly_k.beq' (rhs'.sub lhs').toPoly_k

theorem le_norm_expr {α} [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_cnstr_cert lhs rhs lhs' rhs' → (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  simp [norm_cnstr_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPoly] at h
  replace h : rhs.denote ctx - lhs.denote ctx = rhs'.denote ctx - lhs'.denote ctx := h
  rw [← OrderedAdd.sub_nonneg_iff, h, OrderedAdd.sub_nonneg_iff]

theorem lt_norm_expr {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_cnstr_cert lhs rhs lhs' rhs' → (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  simp [norm_cnstr_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPoly] at h
  replace h : rhs.denote ctx - lhs.denote ctx = rhs'.denote ctx - lhs'.denote ctx := h
  rw [← OrderedAdd.sub_pos_iff, h, OrderedAdd.sub_pos_iff]

noncomputable def norm_eq_cert (lhs rhs lhs' rhs' : Expr) : Bool :=
  (lhs.sub rhs).toPoly_k.beq' (lhs'.sub rhs').toPoly_k

theorem eq_norm_expr {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_eq_cert lhs rhs lhs' rhs' → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  simp [norm_eq_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPoly] at h
  replace h : lhs.denote ctx - rhs.denote ctx = lhs'.denote ctx - rhs'.denote ctx := h
  rw [← AddCommGroup.sub_eq_zero_iff, h, AddCommGroup.sub_eq_zero_iff]

noncomputable def norm_cnstr_nc_cert (lhs rhs lhs' rhs' : Expr) : Bool :=
  (rhs.sub lhs).toPoly_nc.beq' (rhs'.sub lhs').toPoly_nc

theorem le_norm_expr_nc {α} [Ring α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_cnstr_nc_cert lhs rhs lhs' rhs' → (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  simp [norm_cnstr_nc_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPoly_nc] at h
  replace h : rhs.denote ctx - lhs.denote ctx = rhs'.denote ctx - lhs'.denote ctx := h
  rw [← OrderedAdd.sub_nonneg_iff, h, OrderedAdd.sub_nonneg_iff]

theorem lt_norm_expr_nc {α} [Ring α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_cnstr_nc_cert lhs rhs lhs' rhs' → (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  simp [norm_cnstr_nc_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPoly_nc] at h
  replace h : rhs.denote ctx - lhs.denote ctx = rhs'.denote ctx - lhs'.denote ctx := h
  rw [← OrderedAdd.sub_pos_iff, h, OrderedAdd.sub_pos_iff]

noncomputable def norm_eq_nc_cert (lhs rhs lhs' rhs' : Expr) : Bool :=
  (lhs.sub rhs).toPoly_nc.beq' (lhs'.sub rhs').toPoly_nc

theorem eq_norm_expr_nc {α} [Ring α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_eq_nc_cert lhs rhs lhs' rhs' → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  simp [norm_eq_nc_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPoly_nc] at h
  replace h : lhs.denote ctx - rhs.denote ctx = lhs'.denote ctx - rhs'.denote ctx := h
  rw [← AddCommGroup.sub_eq_zero_iff, h, AddCommGroup.sub_eq_zero_iff]

/-!
Helper theorems for quick normalization
-/

theorem le_norm0 {α} [Ring α] [LE α] (lhs rhs : α) : (lhs ≤ rhs) = (lhs ≤ rhs + Int.cast (R := α) 0) := by
  rw [Ring.intCast_zero, Semiring.add_zero]

theorem lt_norm0 {α} [Ring α] [LT α] (lhs rhs : α) : (lhs < rhs) = (lhs < rhs + Int.cast (R := α) 0) := by
  rw [Ring.intCast_zero, Semiring.add_zero]

theorem eq_norm0 {α} [Ring α] (lhs rhs : α) : (lhs = rhs) = (lhs = rhs + Int.cast (R := α) 0) := by
  rw [Ring.intCast_zero, Semiring.add_zero]

end Lean.Grind.CommRing
