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
public import Init.Data.Int.Kernel
public import Init.Data.RArray
public import Init.Ext
import Init.Data.Hashable
import Init.Data.Int.LemmasAux
import Init.Data.Nat.Internal.Linear
import Init.Grind.Ordered.Order
import Init.Omega
import Init.WFTactics
import Init.Data.Int.Repr
public import Init.Data.Nat.Gcd

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
  Int.rec (fun n => OfNat.ofNat (α := α) n) (fun n => - OfNat.ofNat (α := α) n.succ) k

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
  Bool.rec false (Nat.beq pw₁.k pw₂.k) (Nat.beq pw₁.x pw₂.x)

@[simp] theorem Power.beq'_eq (pw₁ pw₂ : Power) : pw₁.beq' pw₂ = (pw₁ = pw₂) := by
  change (Nat.beq pw₁.x pw₂.x && Nat.beq pw₁.k pw₂.k) = (pw₁ = pw₂)
  cases pw₁; cases pw₂; simp

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
    (fun pw₁ _ ih m₂ => Mon.rec false (fun pw₂ m₂ _ =>
      Bool.rec false (Bool.rec false (ih m₂) (Nat.beq pw₁.k pw₂.k)) (Nat.beq pw₁.x pw₂.x)) m₂) m₁

@[simp] theorem Mon.beq'_eq (m₁ m₂ : Mon) : m₁.beq' m₂ = (m₁ = m₂) := by
  induction m₁ generalizing m₂ with
  | unit => cases m₂ <;> simp [Mon.beq']
  | mult pw₁ m₁ ih =>
    cases m₂ with
    | unit => simp [Mon.beq']
    | mult pw₂ m₂ =>
      change (Nat.beq pw₁.x pw₂.x && (Nat.beq pw₁.k pw₂.k && m₁.beq' m₂)) = (_ = _)
      cases pw₁; cases pw₂
      simp [ih, and_assoc]

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

def Mon.mul (m₁ m₂ : Mon) : Mon :=
  go (m₁.length + m₂.length + 1) m₁ m₂
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

/-!
Kernel-reduction variants of the monomial and polynomial operations, written with recursors,
`Bool.rec` and the operations of `Init.Data.Int.Kernel`, for use in certificates. A function that
merges two sorted lists recurses on the first one, and on the second one in a nested recursor
whose induction hypothesis handles the steps where only the second list shrinks.
-/

noncomputable def Mon.mul_k (m₁ : Mon) : Mon → Mon :=
  Mon.rec (motive := fun _ => Mon → Mon)
    (fun m₂ => m₂)
    (fun pw₁ m₁ ih₁ m₂ =>
      Mon.rec (motive := fun _ => Mon)
        (.mult pw₁ m₁)
        (fun pw₂ m₂ ih₂ =>
          Bool.rec
            (Bool.rec
              (.mult { x := pw₁.x, k := Nat.add pw₁.k pw₂.k } (ih₁ m₂))
              (.mult pw₂ ih₂)
              (Nat.blt pw₂.x pw₁.x))
            (.mult pw₁ (ih₁ (.mult pw₂ m₂)))
            (Nat.blt pw₁.x pw₂.x))
        m₂)
    m₁

theorem Mon.mul_k_eq_mul_go (fuel : Nat) (m₁ m₂ : Mon) (h : m₁.length + m₂.length < fuel) :
    Mon.mul_k m₁ m₂ = Mon.mul.go fuel m₁ m₂ := by
  induction fuel generalizing m₁ m₂ with
  | zero => contradiction
  | succ fuel ih =>
    cases m₁ with
    | unit => cases m₂ <;> rfl
    | mult pw₁ m₁ =>
      cases m₂ with
      | unit => rfl
      | mult pw₂ m₂ =>
        simp only [Mon.length] at h
        change Bool.rec (motive := fun _ => Mon) _ _ (Nat.blt pw₁.x pw₂.x) = _
        simp only [Mon.mul.go, Power.varLt, cond_eq_ite]
        cases h₁ : Nat.blt pw₁.x pw₂.x
        · cases h₂ : Nat.blt pw₂.x pw₁.x
          · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; exact ih _ _ (by omega)
          · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; exact ih (.mult pw₁ m₁) m₂ (by simp [Mon.length]; omega)
        · simp only [↓reduceIte]; congr 1; exact ih m₁ (.mult pw₂ m₂) (by simp [Mon.length]; omega)

@[simp] theorem Mon.mul_k_eq_mul (m₁ m₂ : Mon) : Mon.mul_k m₁ m₂ = Mon.mul m₁ m₂ :=
  Mon.mul_k_eq_mul_go _ _ _ (Nat.lt_succ_self _)

def Mon.mul_nc (m₁ m₂ : Mon) : Mon :=
  match m₁ with
  | .unit          => m₂
  | .mult pw .unit => m₂.mulPow_nc pw
  | .mult pw m₁    => .mult pw (mul_nc m₁ m₂)

def Mon.degree : Mon → Nat
  | .unit => 0
  | .mult pw m => pw.k + degree m

noncomputable def Mon.degree_k (m : Mon) : Nat :=
  Mon.rec 0 (fun pw _ ih => Nat.add pw.k ih) m

@[simp] theorem Mon.degree_k_eq_degree (m : Mon) : Mon.degree_k m = Mon.degree m := by
  induction m with
  | unit => rfl
  | mult pw m ih => change Nat.add pw.k m.degree_k = _; rw [ih]; rfl

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
  revlexFuel (m₁.length + m₂.length + 1) m₁ m₂

def Mon.grevlex (m₁ m₂ : Mon) : Ordering :=
  compare m₁.degree m₂.degree |>.then (revlex m₁ m₂)

noncomputable def Mon.revlex_k (m₁ : Mon) : Mon → Ordering :=
  Mon.rec (motive := fun _ => Mon → Ordering)
    (fun m₂ => Mon.rec .eq (fun _ _ _ => .gt) m₂)
    (fun pw₁ _ ih₁ m₂ =>
      Mon.rec (motive := fun _ => Ordering)
        .lt
        (fun pw₂ m₂ ih₂ =>
          Bool.rec
            (Bool.rec (ih₂.then' .gt) ((ih₁ (.mult pw₂ m₂)).then' .lt) (Nat.blt pw₁.x pw₂.x))
            ((ih₁ m₂).then' (powerRevlex_k pw₁.k pw₂.k))
            (Nat.beq pw₁.x pw₂.x))
        m₂)
    m₁

noncomputable def Mon.grevlex_k (m₁ m₂ : Mon) : Ordering :=
  Bool.rec
    (Bool.rec .gt .lt (Nat.blt m₁.degree_k m₂.degree_k))
    (revlex_k m₁ m₂)
    (Nat.beq m₁.degree_k m₂.degree_k)

theorem Mon.revlex_k_eq_revlexWF (m₁ m₂ : Mon) : m₁.revlex_k m₂ = m₁.revlexWF m₂ := by
  fun_induction revlexWF
  case case1 => rfl
  case case2 => rfl
  case case3 => rfl
  case case4 pw₁ m₁ pw₂ m₂ h ih =>
    have h : Nat.beq pw₁.x pw₂.x = true := by simpa using h
    change Bool.rec (motive := fun _ => Ordering) _ _ (Nat.beq pw₁.x pw₂.x) = _
    rw [h]; dsimp only; rw [← ih, Ordering.then'_eq_then, powerRevlex_k_eq_powerRevlex]; rfl
  case case5 pw₁ m₁ pw₂ m₂ h₁ h₂ ih =>
    have h₁ : Nat.beq pw₁.x pw₂.x = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; simpa using h₁
    change Bool.rec (motive := fun _ => Ordering) _ _ (Nat.beq pw₁.x pw₂.x) = _
    rw [h₁]; dsimp only; rw [h₂]; dsimp only; rw [← ih, Ordering.then'_eq_then]; rfl
  case case6 pw₁ m₁ pw₂ m₂ h₁ h₂ ih =>
    have h₁ : Nat.beq pw₁.x pw₂.x = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; simpa using h₁
    have h₂ : Nat.blt pw₁.x pw₂.x = false := by simpa using h₂
    change Bool.rec (motive := fun _ => Ordering) _ _ (Nat.beq pw₁.x pw₂.x) = _
    rw [h₁]; dsimp only; rw [h₂]; dsimp only; rw [← ih, Ordering.then'_eq_then]; rfl

theorem Mon.revlexFuel_eq_revlexWF (fuel : Nat) (m₁ m₂ : Mon) : revlexFuel fuel m₁ m₂ = revlexWF m₁ m₂ := by
  fun_induction revlexFuel
  case case1 => rfl
  all_goals simp_all [revlexWF]

@[simp] theorem Mon.revlex_k_eq_revlex (m₁ m₂ : Mon) : m₁.revlex_k m₂ = m₁.revlex m₂ := by
  rw [revlex_k_eq_revlexWF, revlex, revlexFuel_eq_revlexWF]

@[simp] theorem Mon.grevlex_k_eq_grevlex (m₁ m₂ : Mon) : m₁.grevlex_k m₂ = m₁.grevlex m₂ := by
  unfold grevlex_k grevlex
  rw [degree_k_eq_degree, degree_k_eq_degree, revlex_k_eq_revlex]
  simp only [compare, compareOfLessAndEq]
  cases h : Nat.beq m₁.degree m₂.degree
  · have h' : m₁.degree ≠ m₂.degree := Nat.ne_of_beq_eq_false h
    simp only [h']
    cases h'' : Nat.blt m₁.degree m₂.degree
    · have : ¬ m₁.degree < m₂.degree := fun h => by simp [Nat.blt_eq.mpr h] at h''
      simp [this]
    · have : m₁.degree < m₂.degree := by simpa using h''
      simp [this]
  · have h' : m₁.degree = m₂.degree := Nat.eq_of_beq_eq_true h
    simp [h']

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
        (fun k₂ v₂ p₂ _ => Bool.rec false (Bool.rec false (ih p₂) (Mon.beq' v₁ v₂)) (Int.beq' k₁ k₂)) p₂)
    p₁

@[simp] theorem Poly.beq'_eq (p₁ p₂ : Poly) : p₁.beq' p₂ = (p₁ = p₂) := by
  induction p₁ generalizing p₂ with
  | num k₁ => cases p₂ <;> simp [Poly.beq']
  | add k₁ m₁ p₁ ih =>
    cases p₂ with
    | num k₂ => simp [Poly.beq']
    | add k₂ m₂ p₂ =>
      change (Int.beq' k₁ k₂ && (Mon.beq' m₁ m₂ && p₁.beq' p₂)) = (_ = _)
      simp [ih]

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
    (Poly.rec (fun k' => .num (Int.add_k k' k)) (fun k' m _ ih => .add k' m ih) p)
    p
    (Int.beqZero_k k)

@[simp] theorem Poly.addConst_k_eq_addConst (p : Poly) (k : Int) : addConst_k p k = addConst p k := by
  unfold addConst_k addConst; rw [Int.beqZero_k_eq, cond_eq_ite]
  cases h : k == 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction p with
    | num k' => show Poly.num (Int.add_k k' k) = _; simp [addConst.go]
    | add k' m p ih => simp only [addConst.go, ← ih]
  · rfl

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
      (Poly.rec (fun k' => .num (Int.mul_k k k')) (fun k' m _ ih => .add (Int.mul_k k k') m ih) p)
      p (Int.beq' k 1))
    (.num 0)
    (Int.beqZero_k k)

@[simp] theorem Poly.mulConst_k_eq_mulConst (k : Int) (p : Poly) : p.mulConst_k k = p.mulConst k := by
  unfold mulConst_k mulConst; rw [Int.beqZero_k_eq, Int.beq'_eq_beq, cond_eq_ite, cond_eq_ite]
  cases h₀ : k == 0
  · cases h₁ : k == 1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      induction p with
      | num k' => show Poly.num (Int.mul_k k k') = _; simp [mulConst.go]
      | add k' m p ih => show Poly.add (Int.mul_k k k') m _ = _; simp only [mulConst.go, ← ih, Int.mul_k_eq]; rfl
    · rfl
  · rfl

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
    (Mon.rec
      (p.mulConst_k k)
      (fun _ _ _ => Poly.rec
        (fun k' => Bool.rec (.add (Int.mul_k k k') m (.num 0)) (.num 0) (Int.beqZero_k k'))
        (fun k' m' _ ih => .add (Int.mul_k k k') (m.mul_k m') ih)
        p)
      m)
    (.num 0)
    (Int.beqZero_k k)

@[simp] theorem Poly.mulMon_k_eq_mulMon (k : Int) (m : Mon) (p : Poly) : p.mulMon_k k m = p.mulMon k m := by
  unfold mulMon_k mulMon; rw [Int.beqZero_k_eq, cond_eq_ite, cond_eq_ite]
  cases h₀ : k == 0
  · cases m with
    | unit => simp [mulConst_k_eq_mulConst]
    | mult pw m =>
      have : (Mon.mult pw m == .unit) = false := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, this]
      induction p with
      | num k' =>
        show Bool.rec (motive := fun _ => Poly) _ _ (Int.beqZero_k k') = _
        rw [Int.beqZero_k_eq]; simp only [mulMon.go, cond_eq_ite, Int.mul_k_eq]
        cases k' == 0 <;> rfl
      | add k' m' p ih =>
        show Poly.add (Int.mul_k k k') ((Mon.mult pw m).mul_k m') _ = _
        simp only [mulMon.go, ← ih, Int.mul_k_eq, Mon.mul_k_eq_mul]; rfl
  · rfl

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

def Poly.length : Poly → Nat
  | .num _ => 0
  | .add _ _ p => 1 + p.length

def Poly.combine (p₁ p₂ : Poly) : Poly :=
  go (p₁.length + p₂.length + 1) p₁ p₂
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

noncomputable def Poly.combine_k (p₁ : Poly) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k₁ p₂ => Poly.rec (fun k₂ => .num (Int.add_k k₁ k₂)) (fun k₂ m₂ p₂ _ => addConst_k (.add k₂ m₂ p₂) k₁) p₂)
    (fun k₁ m₁ p₁ ih₁ p₂ =>
      Poly.rec (motive := fun _ => Poly)
        (fun k₂ => addConst_k (.add k₁ m₁ p₁) k₂)
        (fun k₂ m₂ p₂ ih₂ =>
          Ordering.rec
            (.add k₂ m₂ ih₂)
            (Bool.rec (.add (Int.add_k k₁ k₂) m₁ (ih₁ p₂)) (ih₁ p₂) (Int.beqZero_k (Int.add_k k₁ k₂)))
            (.add k₁ m₁ (ih₁ (.add k₂ m₂ p₂)))
            (m₁.grevlex_k m₂))
        p₂)
    p₁

theorem Poly.combine_k_eq_combine_go (fuel : Nat) (p₁ p₂ : Poly) (h : p₁.length + p₂.length < fuel) :
    p₁.combine_k p₂ = Poly.combine.go fuel p₁ p₂ := by
  induction fuel generalizing p₁ p₂ with
  | zero => contradiction
  | succ fuel ih =>
    cases p₁ with
    | num k₁ =>
      cases p₂ with
      | num k₂ => show Poly.num (Int.add_k k₁ k₂) = _; simp [combine.go]
      | add k₂ m₂ p₂ => exact addConst_k_eq_addConst (.add k₂ m₂ p₂) k₁
    | add k₁ m₁ p₁ =>
      cases p₂ with
      | num k₂ => exact addConst_k_eq_addConst (.add k₁ m₁ p₁) k₂
      | add k₂ m₂ p₂ =>
        simp only [Poly.length] at h
        change Ordering.rec (motive := fun _ => Poly) _ _ _ (m₁.grevlex_k m₂) = _
        rw [Mon.grevlex_k_eq_grevlex]; simp only [combine.go]
        cases m₁.grevlex m₂ with
        | lt => dsimp only; congr 1; exact ih (.add k₁ m₁ p₁) p₂ (by simp [Poly.length]; omega)
        | gt => dsimp only; congr 1; exact ih p₁ (.add k₂ m₂ p₂) (by simp [Poly.length]; omega)
        | eq =>
          dsimp only; rw [Int.beqZero_k_eq, Int.add_k_eq, cond_eq_ite]
          cases (Int.add k₁ k₂ == 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; exact ih p₁ p₂ (by omega)
          · exact ih p₁ p₂ (by omega)

@[simp] theorem Poly.combine_k_eq_combine (p₁ p₂ : Poly) : p₁.combine_k p₂ = p₁.combine p₂ :=
  combine_k_eq_combine_go _ _ _ (Nat.lt_succ_self _)

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

noncomputable def Poly.mul_k (p₁ p₂ : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k acc => acc.combine_k (p₂.mulConst_k k))
    (fun k m _ ih acc => ih (acc.combine_k (p₂.mulMon_k k m)))
    p₁ (.num 0)

@[simp] theorem Poly.mul_k_eq_mul (p₁ p₂ : Poly) : p₁.mul_k p₂ = p₁.mul p₂ := by
  unfold mul_k mul; generalize Poly.num 0 = acc
  induction p₁ generalizing acc with
  | num k => simp [mul.go]
  | add k m p₁ ih => simp only [mul.go, ← ih, combine_k_eq_combine, mulMon_k_eq_mulMon]

noncomputable def Poly.pow_k (p : Poly) (k : Nat) : Poly :=
  Nat.rec (.num 1) (fun k ih => Bool.rec (p.mul_k ih) p (Nat.beq k 0)) k

@[simp] theorem Poly.pow_k_eq_pow (p : Poly) (k : Nat) : p.pow_k k = p.pow k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Bool.rec (motive := fun _ => Poly) (p.mul_k (p.pow_k k)) p (Nat.beq k 0) = _
    cases k with
    | zero => rfl
    | succ k => simp only [Nat.beq, ih, mul_k_eq_mul]; rfl

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
    (fun _ ih => ih.mulConst_k (Int.negSucc 0))
    (fun _ _ ih₁ ih₂ => ih₁.combine_k ih₂)
    (fun _ _ ih₁ ih₂ => ih₁.combine_k (ih₂.mulConst_k (Int.negSucc 0)))
    (fun _ _ ih₁ ih₂ => ih₁.mul_k ih₂)
    (fun a k ih => Bool.rec
      (Expr.rec (fun n => .num (Int.pow_k n k)) (fun n => .num (Int.ofNat (Nat.pow n k))) (fun n => .num (Int.pow_k n k))
        (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => ih.pow_k k)
        (fun _ _ _ _ => ih.pow_k k)
        (fun _ _ _ _ => ih.pow_k k)
        (fun _ _ _ _ => ih.pow_k k)
        (fun _ _ _ => ih.pow_k k)
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

def Poly.gcdCoeffs : Poly → Nat
  | .num k => k.natAbs
  | .add k _ p => go p k.natAbs
where
  go (p : Poly) (acc : Nat) : Nat :=
    if acc == 1 then
      acc
    else match p with
      | .num k => Nat.gcd acc k.natAbs
      | .add k _ p => go p (Nat.gcd acc k.natAbs)

def Poly.divConst (p : Poly) (a : Int) : Poly :=
  match p with
  | .num k => .num (k / a)
  | .add k m p => .add (k / a) m (divConst p a)

def Poly.maxDegreeOf (p : Poly) (x : Var) : Nat :=
  go p 0
where
  go (p : Poly) (max : Nat) : Nat :=
    match p with
    | .num _ => max
    | .add _ m p => go p (Nat.max max (m.degreeOf x))

@[simp] theorem Expr.toPoly_k_eq_toPoly (e : Expr) : e.toPoly_k = e.toPoly := by
  induction e <;> simp only [toPoly, toPoly_k]
  next a ih => rw [Poly.mulConst_k_eq_mulConst]; congr
  case add => rw [← Poly.combine_k_eq_combine]; congr
  case sub => rw [← Poly.combine_k_eq_combine, ← Poly.mulConst_k_eq_mulConst]; congr
  case mul => rw [← Poly.mul_k_eq_mul]; congr
  case pow a k ih =>
    rw [cond_eq_ite]; split
    next h => rw [Nat.beq_eq_true_eq, ← Nat.beq_eq] at h; rw [h]
    next h =>
      rw [Nat.beq_eq_true_eq, ← Nat.beq_eq, Bool.not_eq_true] at h; rw [h]; dsimp only
      show
        (Expr.rec (fun n => .num (Int.pow_k n k)) (fun n => .num (Int.ofNat (Nat.pow n k))) (fun n => .num (Int.pow_k n k))
          (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => a.toPoly_k.pow_k k)
          (fun _ _ _ _ => a.toPoly_k.pow_k k)
          (fun _ _ _ _ => a.toPoly_k.pow_k k)
          (fun _ _ _ _ => a.toPoly_k.pow_k k)
          (fun _ _ _ => a.toPoly_k.pow_k k)
          a) = match a with
            | num n => Poly.num (n ^ k)
            | .intCast n => .num (n^k)
            | .natCast n => .num (n^k)
            | var x => Poly.ofMon (Mon.mult { x := x, k := k } Mon.unit)
            | x => a.toPoly.pow k
      cases a <;> simp [*, Int.pow_k_eq] <;> rfl

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

/-! Kernel-reduction variants of the definitions for the `IsCharP` case. -/

noncomputable def Poly.addConstC_k (p : Poly) (k : Int) (c : Nat) : Poly :=
  Poly.rec (fun k' => .num (Int.emod_k (Int.add_k k' k) (Int.ofNat c))) (fun k' m _ ih => .add k' m ih) p

@[simp] theorem Poly.addConstC_k_eq_addConstC (p : Poly) (k : Int) (c : Nat) : p.addConstC_k k c = p.addConstC k c := by
  induction p with
  | num k' => show Poly.num (Int.emod_k (Int.add_k k' k) (Int.ofNat c)) = _; simp [addConstC]
  | add k' m p ih => show Poly.add k' m (p.addConstC_k k c) = _; rw [ih]; rfl

noncomputable def Poly.insertC_k.go (k : Int) (m : Mon) (c : Nat) (p : Poly) : Poly :=
  Poly.rec (fun k' => .add k m (.num k'))
    (fun k' m' p ih => Ordering.rec
      (.add k' m' ih)
      (Bool.rec (.add (Int.emod_k (Int.add_k k k') (Int.ofNat c)) m p) p
        (Int.beqZero_k (Int.emod_k (Int.add_k k k') (Int.ofNat c))))
      (.add k m (.add k' m' p))
      (m.grevlex_k m'))
    p

noncomputable def Poly.insertC_k (k : Int) (m : Mon) (p : Poly) (c : Nat) : Poly :=
  Bool.rec (insertC_k.go (Int.emod_k k (Int.ofNat c)) m c p) p (Int.beqZero_k (Int.emod_k k (Int.ofNat c)))

@[simp] theorem Poly.insertC_k_eq_insertC (k : Int) (m : Mon) (p : Poly) (c : Nat) : p.insertC_k k m c = p.insertC k m c := by
  have hgo : ∀ k p, insertC_k.go k m c p = insertC.go m c k p := by
    intro k p
    induction p with
    | num k' => rfl
    | add k' m' p ih =>
      change Ordering.rec (motive := fun _ => Poly) _ _ _ (m.grevlex_k m') = _
      rw [Mon.grevlex_k_eq_grevlex]; simp only [insertC.go]
      cases m.grevlex m' with
      | lt => exact congrArg _ ih
      | eq =>
        dsimp only; rw [Int.beqZero_k_eq, Int.emod_k_eq, Int.add_k_eq, cond_eq_ite]
        cases ((Int.add k k') % (Int.ofNat c) == 0) <;> rfl
      | gt => rfl
  unfold insertC_k insertC; rw [Int.beqZero_k_eq, Int.emod_k_eq, cond_eq_ite]
  cases h : (k % Int.ofNat c == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact hgo _ _
  · rfl

noncomputable def Poly.mulConstC_k.go (k : Int) (c : Nat) (p : Poly) : Poly :=
  Poly.rec (fun k' => .num (Int.emod_k (Int.mul_k k k') (Int.ofNat c)))
    (fun k' m _ ih => Bool.rec (.add (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) m ih) ih
      (Int.beqZero_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c))))
    p

noncomputable def Poly.mulConstC_k (k : Int) (p : Poly) (c : Nat) : Poly :=
  Bool.rec
    (Bool.rec (mulConstC_k.go k c p) p (Int.beq' (Int.emod_k k (Int.ofNat c)) 1))
    (.num 0)
    (Int.beqZero_k (Int.emod_k k (Int.ofNat c)))

@[simp] theorem Poly.mulConstC_k_eq_mulConstC (k : Int) (p : Poly) (c : Nat) : p.mulConstC_k k c = p.mulConstC k c := by
  have hgo : ∀ k p, mulConstC_k.go k c p = mulConstC.go k c p := by
    intro k p
    induction p with
    | num k' => show Poly.num (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) = _; simp [mulConstC.go]
    | add k' m p ih =>
      change Bool.rec (motive := fun _ => Poly) _ _ (Int.beqZero_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c))) = _
      rw [Int.beqZero_k_eq, Int.emod_k_eq, Int.mul_k_eq]; simp only [mulConstC.go, cond_eq_ite]
      cases (Int.mul k k' % Int.ofNat c == 0) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | rfl | exact congrArg _ ih | exact ih
  unfold mulConstC_k mulConstC; rw [Int.beqZero_k_eq, Int.beq'_eq_beq, Int.emod_k_eq, cond_eq_ite, cond_eq_ite]
  cases (k % Int.ofNat c == 0)
  · cases (k % Int.ofNat c == 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hgo _ _
    · rfl
  · rfl

noncomputable def Poly.mulMonC_k.go (k : Int) (m : Mon) (c : Nat) (p : Poly) : Poly :=
  Poly.rec
    (fun k' => Bool.rec (.add (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) m (.num 0)) (.num 0)
      (Int.beqZero_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c))))
    (fun k' m' _ ih => Bool.rec (.add (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) (m.mul_k m') ih) ih
      (Int.beqZero_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c))))
    p

noncomputable def Poly.mulMonC_k (k : Int) (m : Mon) (p : Poly) (c : Nat) : Poly :=
  Bool.rec
    (Mon.rec (p.mulConstC_k (Int.emod_k k (Int.ofNat c)) c) (fun _ _ _ => mulMonC_k.go k m c p) m)
    (.num 0)
    (Int.beqZero_k (Int.emod_k k (Int.ofNat c)))

@[simp] theorem Poly.mulMonC_k_eq_mulMonC (k : Int) (m : Mon) (p : Poly) (c : Nat) : p.mulMonC_k k m c = p.mulMonC k m c := by
  have hgo : ∀ k p, mulMonC_k.go k m c p = mulMonC.go k m c p := by
    intro k p
    induction p with
    | num k' =>
      change Bool.rec (motive := fun _ => Poly) _ _ (Int.beqZero_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c))) = _
      rw [Int.beqZero_k_eq, Int.emod_k_eq, Int.mul_k_eq]; simp only [mulMonC.go, cond_eq_ite]
      cases (Int.mul k k' % Int.ofNat c == 0) <;> rfl
    | add k' m' p ih =>
      change Bool.rec (motive := fun _ => Poly) _ _ (Int.beqZero_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c))) = _
      rw [Int.beqZero_k_eq, Int.emod_k_eq, Int.mul_k_eq]; simp only [mulMonC.go, cond_eq_ite]
      cases (Int.mul k k' % Int.ofNat c == 0) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact ih | (rw [Mon.mul_k_eq_mul]; exact congrArg _ ih)
  unfold mulMonC_k mulMonC; rw [Int.beqZero_k_eq, Int.emod_k_eq, cond_eq_ite, cond_eq_ite]
  cases (k % Int.ofNat c == 0)
  · cases m with
    | unit => simp [mulConstC_k_eq_mulConstC]
    | mult pw m =>
      have : (Mon.mult pw m == .unit) = false := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, this]; exact hgo _ _
  · rfl

noncomputable def Poly.combineC_k (p₁ : Poly) (c : Nat) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k₁ p₂ => Poly.rec (fun k₂ => .num (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c)))
      (fun k₂ m₂ p₂ _ => addConstC_k (.add k₂ m₂ p₂) k₁ c) p₂)
    (fun k₁ m₁ p₁ ih₁ p₂ =>
      Poly.rec (motive := fun _ => Poly)
        (fun k₂ => addConstC_k (.add k₁ m₁ p₁) k₂ c)
        (fun k₂ m₂ p₂ ih₂ =>
          Ordering.rec
            (.add k₂ m₂ ih₂)
            (Bool.rec (.add (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c)) m₁ (ih₁ p₂)) (ih₁ p₂)
              (Int.beqZero_k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c))))
            (.add k₁ m₁ (ih₁ (.add k₂ m₂ p₂)))
            (m₁.grevlex_k m₂))
        p₂)
    p₁

@[simp] theorem Poly.combineC_k_eq_combineC (p₁ p₂ : Poly) (c : Nat) : p₁.combineC_k c p₂ = p₁.combineC p₂ c := by
  fun_induction Poly.combineC
  case case1 k₁ k₂ => show Poly.num (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c)) = _; simp
  case case2 k₁ k₂ m₂ p₂ => exact addConstC_k_eq_addConstC (.add k₂ m₂ p₂) k₁ c
  case case3 k₁ m₁ p₁ k₂ => exact addConstC_k_eq_addConstC (.add k₁ m₁ p₁) k₂ c
  case case4 k₁ m₁ p₁ k₂ m₂ p₂ h k h' ih =>
    change Ordering.rec (motive := fun _ => Poly) _ _ _ (m₁.grevlex_k m₂) = _
    rw [Mon.grevlex_k_eq_grevlex, h]; dsimp only
    rw [Int.beqZero_k_eq, Int.emod_k_eq, Int.add_k_eq]
    simp only [k] at h'
    rw [show ((Int.add k₁ k₂) % (Int.ofNat c) == 0) = true from h']; exact ih
  case case5 k₁ m₁ p₁ k₂ m₂ p₂ h k h' ih =>
    change Ordering.rec (motive := fun _ => Poly) _ _ _ (m₁.grevlex_k m₂) = _
    rw [Mon.grevlex_k_eq_grevlex, h]; dsimp only
    rw [Int.beqZero_k_eq, Int.emod_k_eq, Int.add_k_eq]
    simp only [k] at h'
    have h'' : ((Int.add k₁ k₂) % (Int.ofNat c) == 0) = false := by simpa using h'
    rw [h'']; exact congrArg _ ih
  case case6 k₁ m₁ p₁ k₂ m₂ p₂ h ih =>
    change Ordering.rec (motive := fun _ => Poly) _ _ _ (m₁.grevlex_k m₂) = _
    rw [Mon.grevlex_k_eq_grevlex, h]; exact congrArg _ ih
  case case7 k₁ m₁ p₁ k₂ m₂ p₂ h ih =>
    change Ordering.rec (motive := fun _ => Poly) _ _ _ (m₁.grevlex_k m₂) = _
    rw [Mon.grevlex_k_eq_grevlex, h]; exact congrArg _ ih

noncomputable def Poly.mulC_k (p₁ p₂ : Poly) (c : Nat) : Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k acc => acc.combineC_k c (p₂.mulConstC_k k c))
    (fun k m _ ih acc => ih (acc.combineC_k c (p₂.mulMonC_k k m c)))
    p₁ (.num 0)

@[simp] theorem Poly.mulC_k_eq_mulC (p₁ p₂ : Poly) (c : Nat) : p₁.mulC_k p₂ c = p₁.mulC p₂ c := by
  unfold mulC_k mulC; generalize Poly.num 0 = acc
  induction p₁ generalizing acc with
  | num k => simp [mulC.go, combineC_k_eq_combineC, mulConstC_k_eq_mulConstC]
  | add k m p₁ ih => simp only [mulC.go, ← ih, combineC_k_eq_combineC, mulMonC_k_eq_mulMonC]

noncomputable def Poly.powC_k (p : Poly) (k : Nat) (c : Nat) : Poly :=
  Nat.rec (.num 1) (fun k ih => Bool.rec (p.mulC_k ih c) p (Nat.beq k 0)) k

@[simp] theorem Poly.powC_k_eq_powC (p : Poly) (k : Nat) (c : Nat) : p.powC_k k c = p.powC k c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Bool.rec (motive := fun _ => Poly) (p.mulC_k (p.powC_k k c) c) p (Nat.beq k 0) = _
    cases k with
    | zero => rfl
    | succ k => simp only [Nat.beq, ih, mulC_k_eq_mulC]; rfl

noncomputable def Expr.toPolyC_k (e : Expr) (c : Nat) : Poly :=
  Expr.rec
    (fun k => .num (Int.emod_k k (Int.ofNat c)))
    (fun k => .num (Int.emod_k (Int.ofNat k) (Int.ofNat c)))
    (fun k => .num (Int.emod_k k (Int.ofNat c)))
    (fun x => .ofVar x)
    (fun _ ih => ih.mulConstC_k (Int.negSucc 0) c)
    (fun _ _ ih₁ ih₂ => ih₁.combineC_k c ih₂)
    (fun _ _ ih₁ ih₂ => ih₁.combineC_k c (ih₂.mulConstC_k (Int.negSucc 0) c))
    (fun _ _ ih₁ ih₂ => ih₁.mulC_k ih₂ c)
    (fun a k ih => Bool.rec
      (Expr.rec (fun n => .num (Int.emod_k (Int.pow_k n k) (Int.ofNat c)))
        (fun _ => ih.powC_k k c) (fun _ => ih.powC_k k c)
        (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => ih.powC_k k c)
        (fun _ _ _ _ => ih.powC_k k c)
        (fun _ _ _ _ => ih.powC_k k c)
        (fun _ _ _ _ => ih.powC_k k c)
        (fun _ _ _ => ih.powC_k k c)
        a)
      (.num 1)
      (k.beq 0))
    e

@[simp] theorem Expr.toPolyC_k_eq_toPolyC (e : Expr) (c : Nat) : e.toPolyC_k c = e.toPolyC c := by
  unfold toPolyC
  induction e with
  | num k => show Poly.num (Int.emod_k k (Int.ofNat c)) = _; simp [toPolyC.go]
  | natCast k => show Poly.num (Int.emod_k (Int.ofNat k) (Int.ofNat c)) = _; simp [toPolyC.go]
  | intCast k => show Poly.num (Int.emod_k k (Int.ofNat c)) = _; simp [toPolyC.go]
  | var x => rfl
  | neg a ih => show (a.toPolyC_k c).mulConstC_k (Int.negSucc 0) c = _; rw [ih, Poly.mulConstC_k_eq_mulConstC]; rfl
  | add a b iha ihb => show (a.toPolyC_k c).combineC_k c (b.toPolyC_k c) = _; rw [iha, ihb, Poly.combineC_k_eq_combineC]; rfl
  | sub a b iha ihb =>
    show (a.toPolyC_k c).combineC_k c ((b.toPolyC_k c).mulConstC_k (Int.negSucc 0) c) = _
    rw [iha, ihb, Poly.mulConstC_k_eq_mulConstC, Poly.combineC_k_eq_combineC]; rfl
  | mul a b iha ihb => show (a.toPolyC_k c).mulC_k (b.toPolyC_k c) c = _; rw [iha, ihb, Poly.mulC_k_eq_mulC]; rfl
  | pow a k ih =>
    simp only [toPolyC.go, cond_eq_ite]
    split
    next h => rw [Nat.beq_eq_true_eq, ← Nat.beq_eq] at h; show Bool.rec (motive := fun _ => Poly) _ _ (k.beq 0) = _; rw [h]
    next h =>
      rw [Nat.beq_eq_true_eq, ← Nat.beq_eq, Bool.not_eq_true] at h
      show Bool.rec (motive := fun _ => Poly) _ _ (k.beq 0) = _
      rw [h]; dsimp only
      show
        (Expr.rec (fun n => .num (Int.emod_k (Int.pow_k n k) (Int.ofNat c)))
          (fun _ => (a.toPolyC_k c).powC_k k c) (fun _ => (a.toPolyC_k c).powC_k k c)
          (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => (a.toPolyC_k c).powC_k k c)
          (fun _ _ _ _ => (a.toPolyC_k c).powC_k k c)
          (fun _ _ _ _ => (a.toPolyC_k c).powC_k k c)
          (fun _ _ _ _ => (a.toPolyC_k c).powC_k k c)
          (fun _ _ _ => (a.toPolyC_k c).powC_k k c)
          a) = match a with
            | .num n => Poly.num ((n ^ k) % c)
            | .var x => Poly.ofMon (Mon.mult { x := x, k := k } Mon.unit)
            | _ => (toPolyC.go c a).powC k c
      cases a <;> simp [*, Int.pow_k_eq, Int.emod_k_eq, Poly.powC_k_eq_powC] <;> rfl

/-! Kernel-reduction variants of `Poly.insert` and of the definitions for the non-commutative case. -/

noncomputable def Poly.insert_k.go (k : Int) (m : Mon) (p : Poly) : Poly :=
  Poly.rec (fun k' => .add k m (.num k'))
    (fun k' m' p ih => Ordering.rec
      (.add k' m' ih)
      (Bool.rec (.add (Int.add_k k k') m p) p (Int.beqZero_k (Int.add_k k k')))
      (.add k m (.add k' m' p))
      (m.grevlex_k m'))
    p

noncomputable def Poly.insert_k (k : Int) (m : Mon) (p : Poly) : Poly :=
  Bool.rec (Mon.rec (p.addConst_k k) (fun _ _ _ => insert_k.go k m p) m) p (Int.beqZero_k k)

@[simp] theorem Poly.insert_k_eq_insert (k : Int) (m : Mon) (p : Poly) : p.insert_k k m = p.insert k m := by
  have hgo : ∀ p, insert_k.go k m p = insert.go k m p := by
    intro p
    induction p with
    | num k' => rfl
    | add k' m' p ih =>
      change Ordering.rec (motive := fun _ => Poly) _ _ _ (m.grevlex_k m') = _
      rw [Mon.grevlex_k_eq_grevlex]; simp only [insert.go]
      cases m.grevlex m' with
      | lt => exact congrArg _ ih
      | eq =>
        dsimp only; rw [Int.beqZero_k_eq, Int.add_k_eq, cond_eq_ite]
        cases (Int.add k k' == 0) <;> rfl
      | gt => rfl
  unfold insert_k insert; rw [Int.beqZero_k_eq, cond_eq_ite, cond_eq_ite]
  cases (k == 0)
  · cases m with
    | unit => simp [addConst_k_eq_addConst]
    | mult pw m =>
      have : (Mon.mult pw m == .unit) = false := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, this]; exact hgo _
  · rfl

noncomputable def Mon.mulPow_nc_k (pw : Power) (m : Mon) : Mon :=
  Mon.rec (.mult pw .unit)
    (fun pw' m _ => Bool.rec (.mult pw (.mult pw' m)) (.mult { x := pw.x, k := Nat.add pw.k pw'.k } m) (Nat.beq pw.x pw'.x))
    m

@[simp] theorem Mon.mulPow_nc_k_eq_mulPow_nc (pw : Power) (m : Mon) : Mon.mulPow_nc_k pw m = Mon.mulPow_nc pw m := by
  cases m with
  | unit => rfl
  | mult pw' m =>
    change Bool.rec (motive := fun _ => Mon) _ _ (Nat.beq pw.x pw'.x) = _
    simp only [mulPow_nc, cond_eq_ite]
    cases h : Nat.beq pw.x pw'.x
    · have : ¬ pw.x = pw'.x := by rw [← Nat.beq_eq, h]; simp
      simp [this]
    · have : pw.x = pw'.x := Nat.eq_of_beq_eq_true h
      simp [this]

noncomputable def Mon.mul_nc_k (m₁ m₂ : Mon) : Mon :=
  Mon.rec (motive := fun _ => Mon) m₂
    (fun pw m₁ ih => Mon.rec (motive := fun _ => Mon) (mulPow_nc_k pw m₂) (fun _ _ _ => .mult pw ih) m₁)
    m₁

@[simp] theorem Mon.mul_nc_k_eq_mul_nc (m₁ m₂ : Mon) : Mon.mul_nc_k m₁ m₂ = Mon.mul_nc m₁ m₂ := by
  induction m₁ with
  | unit => rfl
  | mult pw m₁ ih =>
    cases m₁ with
    | unit => exact mulPow_nc_k_eq_mulPow_nc pw m₂
    | mult pw' m₁ =>
      change Mon.mult pw (Mon.mul_nc_k (.mult pw' m₁) m₂) = _
      rw [ih]; rfl

noncomputable def Poly.mulMon_nc_k.go (k : Int) (m : Mon) (p : Poly) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k' acc => acc.insert_k (Int.mul_k k k') m)
    (fun k' m' _ ih acc => ih (acc.insert_k (Int.mul_k k k') (m.mul_nc_k m')))
    p

noncomputable def Poly.mulMon_nc_k (k : Int) (m : Mon) (p : Poly) : Poly :=
  Bool.rec (Mon.rec (p.mulConst_k k) (fun _ _ _ => mulMon_nc_k.go k m p (.num 0)) m) (.num 0) (Int.beqZero_k k)

@[simp] theorem Poly.mulMon_nc_k_eq_mulMon_nc (k : Int) (m : Mon) (p : Poly) : p.mulMon_nc_k k m = p.mulMon_nc k m := by
  have hgo : ∀ p acc, mulMon_nc_k.go k m p acc = mulMon_nc.go k m p acc := by
    intro p
    induction p with
    | num k' => intro acc; show acc.insert_k (Int.mul_k k k') m = _; simp [mulMon_nc.go]
    | add k' m' p ih =>
      intro acc
      show mulMon_nc_k.go k m p (acc.insert_k (Int.mul_k k k') (m.mul_nc_k m')) = _
      rw [ih]; simp [mulMon_nc.go]
  unfold mulMon_nc_k mulMon_nc; rw [Int.beqZero_k_eq, cond_eq_ite, cond_eq_ite]
  cases (k == 0)
  · cases m with
    | unit => simp [mulConst_k_eq_mulConst]
    | mult pw m =>
      have : (Mon.mult pw m == .unit) = false := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, this]; exact hgo _ _
  · rfl

noncomputable def Poly.mul_nc_k (p₁ p₂ : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k acc => acc.combine_k (p₂.mulConst_k k))
    (fun k m _ ih acc => ih (acc.combine_k (p₂.mulMon_nc_k k m)))
    p₁ (.num 0)

@[simp] theorem Poly.mul_nc_k_eq_mul_nc (p₁ p₂ : Poly) : p₁.mul_nc_k p₂ = p₁.mul_nc p₂ := by
  unfold mul_nc_k mul_nc; generalize Poly.num 0 = acc
  induction p₁ generalizing acc with
  | num k => simp [mul_nc.go]
  | add k m p₁ ih => simp only [mul_nc.go, ← ih, combine_k_eq_combine, mulMon_nc_k_eq_mulMon_nc]

noncomputable def Poly.pow_nc_k (p : Poly) (k : Nat) : Poly :=
  Nat.rec (.num 1) (fun k ih => Bool.rec (ih.mul_nc_k p) p (Nat.beq k 0)) k

@[simp] theorem Poly.pow_nc_k_eq_pow_nc (p : Poly) (k : Nat) : p.pow_nc_k k = p.pow_nc k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Bool.rec (motive := fun _ => Poly) ((p.pow_nc_k k).mul_nc_k p) p (Nat.beq k 0) = _
    cases k with
    | zero => rfl
    | succ k => simp only [Nat.beq, ih, mul_nc_k_eq_mul_nc]; rfl

noncomputable def Expr.toPoly_nc_k (e : Expr) : Poly :=
  Expr.rec
    (fun k => .num k) (fun k => .num k) (fun k => .num k)
    (fun x => .ofVar x)
    (fun _ ih => ih.mulConst_k (Int.negSucc 0))
    (fun _ _ ih₁ ih₂ => ih₁.combine_k ih₂)
    (fun _ _ ih₁ ih₂ => ih₁.combine_k (ih₂.mulConst_k (Int.negSucc 0)))
    (fun _ _ ih₁ ih₂ => ih₁.mul_nc_k ih₂)
    (fun a k ih => Bool.rec
      (Expr.rec (fun n => .num (Int.pow_k n k)) (fun n => .num (Int.ofNat (Nat.pow n k))) (fun n => .num (Int.pow_k n k))
        (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => ih.pow_nc_k k)
        (fun _ _ _ _ => ih.pow_nc_k k)
        (fun _ _ _ _ => ih.pow_nc_k k)
        (fun _ _ _ _ => ih.pow_nc_k k)
        (fun _ _ _ => ih.pow_nc_k k)
        a)
      (.num 1)
      (k.beq 0))
    e

@[simp] theorem Expr.toPoly_nc_k_eq_toPoly_nc (e : Expr) : e.toPoly_nc_k = e.toPoly_nc := by
  induction e <;> simp only [toPoly_nc, toPoly_nc_k]
  next a ih => rw [Poly.mulConst_k_eq_mulConst]; congr
  case add => rw [← Poly.combine_k_eq_combine]; congr
  case sub => rw [← Poly.combine_k_eq_combine, ← Poly.mulConst_k_eq_mulConst]; congr
  case mul => rw [← Poly.mul_nc_k_eq_mul_nc]; congr
  case pow a k ih =>
    rw [cond_eq_ite]; split
    next h => rw [Nat.beq_eq_true_eq, ← Nat.beq_eq] at h; rw [h]
    next h =>
      rw [Nat.beq_eq_true_eq, ← Nat.beq_eq, Bool.not_eq_true] at h; rw [h]; dsimp only
      show
        (Expr.rec (fun n => .num (Int.pow_k n k)) (fun n => .num (Int.ofNat (Nat.pow n k))) (fun n => .num (Int.pow_k n k))
          (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => a.toPoly_nc_k.pow_nc_k k)
          (fun _ _ _ _ => a.toPoly_nc_k.pow_nc_k k)
          (fun _ _ _ _ => a.toPoly_nc_k.pow_nc_k k)
          (fun _ _ _ _ => a.toPoly_nc_k.pow_nc_k k)
          (fun _ _ _ => a.toPoly_nc_k.pow_nc_k k)
          a) = match a with
            | num n => Poly.num (n ^ k)
            | .intCast n => .num (n^k)
            | .natCast n => .num (n^k)
            | var x => Poly.ofMon (Mon.mult { x := x, k := k } Mon.unit)
            | x => a.toPoly_nc.pow_nc k
      cases a <;> simp [*, Int.pow_k_eq] <;> rfl

noncomputable def Poly.mulMonC_nc_k.go (k : Int) (m : Mon) (c : Nat) (p : Poly) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k' acc => acc.insert_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) m)
    (fun k' m' _ ih acc => ih (acc.insert_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) (m.mul_nc_k m')))
    p

noncomputable def Poly.mulMonC_nc_k (k : Int) (m : Mon) (p : Poly) (c : Nat) : Poly :=
  Bool.rec
    (Mon.rec (p.mulConstC_k (Int.emod_k k (Int.ofNat c)) c) (fun _ _ _ => mulMonC_nc_k.go k m c p (.num 0)) m)
    (.num 0)
    (Int.beqZero_k (Int.emod_k k (Int.ofNat c)))

@[simp] theorem Poly.mulMonC_nc_k_eq_mulMonC_nc (k : Int) (m : Mon) (p : Poly) (c : Nat) :
    p.mulMonC_nc_k k m c = p.mulMonC_nc k m c := by
  have hgo : ∀ p acc, mulMonC_nc_k.go k m c p acc = mulMonC_nc.go k m c p acc := by
    intro p
    induction p with
    | num k' => intro acc; show acc.insert_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) m = _; simp [mulMonC_nc.go]
    | add k' m' p ih =>
      intro acc
      show mulMonC_nc_k.go k m c p (acc.insert_k (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) (m.mul_nc_k m')) = _
      rw [ih]; simp [mulMonC_nc.go]
  unfold mulMonC_nc_k mulMonC_nc; rw [Int.beqZero_k_eq, Int.emod_k_eq, cond_eq_ite, cond_eq_ite]
  cases (k % Int.ofNat c == 0)
  · cases m with
    | unit => simp [mulConstC_k_eq_mulConstC]
    | mult pw m =>
      have : (Mon.mult pw m == .unit) = false := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, this]; exact hgo _ _
  · rfl

noncomputable def Poly.mulC_nc_k (p₁ p₂ : Poly) (c : Nat) : Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k acc => acc.combineC_k c (p₂.mulConstC_k k c))
    (fun k m _ ih acc => ih (acc.combineC_k c (p₂.mulMonC_nc_k k m c)))
    p₁ (.num 0)

@[simp] theorem Poly.mulC_nc_k_eq_mulC_nc (p₁ p₂ : Poly) (c : Nat) : p₁.mulC_nc_k p₂ c = p₁.mulC_nc p₂ c := by
  unfold mulC_nc_k mulC_nc; generalize Poly.num 0 = acc
  induction p₁ generalizing acc with
  | num k => simp [mulC_nc.go, combineC_k_eq_combineC, mulConstC_k_eq_mulConstC]
  | add k m p₁ ih => simp only [mulC_nc.go, ← ih, combineC_k_eq_combineC, mulMonC_nc_k_eq_mulMonC_nc]

noncomputable def Poly.powC_nc_k (p : Poly) (k : Nat) (c : Nat) : Poly :=
  Nat.rec (.num 1) (fun k ih => Bool.rec (ih.mulC_nc_k p c) p (Nat.beq k 0)) k

@[simp] theorem Poly.powC_nc_k_eq_powC_nc (p : Poly) (k : Nat) (c : Nat) : p.powC_nc_k k c = p.powC_nc k c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Bool.rec (motive := fun _ => Poly) ((p.powC_nc_k k c).mulC_nc_k p c) p (Nat.beq k 0) = _
    cases k with
    | zero => rfl
    | succ k => simp only [Nat.beq, ih, mulC_nc_k_eq_mulC_nc]; rfl

noncomputable def Expr.toPolyC_nc_k (e : Expr) (c : Nat) : Poly :=
  Expr.rec
    (fun k => .num (Int.emod_k k (Int.ofNat c)))
    (fun k => .num (Int.emod_k (Int.ofNat k) (Int.ofNat c)))
    (fun k => .num (Int.emod_k k (Int.ofNat c)))
    (fun x => .ofVar x)
    (fun _ ih => ih.mulConstC_k (Int.negSucc 0) c)
    (fun _ _ ih₁ ih₂ => ih₁.combineC_k c ih₂)
    (fun _ _ ih₁ ih₂ => ih₁.combineC_k c (ih₂.mulConstC_k (Int.negSucc 0) c))
    (fun _ _ ih₁ ih₂ => ih₁.mulC_nc_k ih₂ c)
    (fun a k ih => Bool.rec
      (Expr.rec (fun n => .num (Int.emod_k (Int.pow_k n k) (Int.ofNat c)))
        (fun _ => ih.powC_nc_k k c) (fun _ => ih.powC_nc_k k c)
        (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => ih.powC_nc_k k c)
        (fun _ _ _ _ => ih.powC_nc_k k c)
        (fun _ _ _ _ => ih.powC_nc_k k c)
        (fun _ _ _ _ => ih.powC_nc_k k c)
        (fun _ _ _ => ih.powC_nc_k k c)
        a)
      (.num 1)
      (k.beq 0))
    e

@[simp] theorem Expr.toPolyC_nc_k_eq_toPolyC_nc (e : Expr) (c : Nat) : e.toPolyC_nc_k c = e.toPolyC_nc c := by
  unfold toPolyC_nc
  induction e with
  | num k => show Poly.num (Int.emod_k k (Int.ofNat c)) = _; simp [toPolyC_nc.go]
  | natCast k => show Poly.num (Int.emod_k (Int.ofNat k) (Int.ofNat c)) = _; simp [toPolyC_nc.go]
  | intCast k => show Poly.num (Int.emod_k k (Int.ofNat c)) = _; simp [toPolyC_nc.go]
  | var x => rfl
  | neg a ih => show (a.toPolyC_nc_k c).mulConstC_k (Int.negSucc 0) c = _; rw [ih, Poly.mulConstC_k_eq_mulConstC]; rfl
  | add a b iha ihb => show (a.toPolyC_nc_k c).combineC_k c (b.toPolyC_nc_k c) = _; rw [iha, ihb, Poly.combineC_k_eq_combineC]; rfl
  | sub a b iha ihb =>
    show (a.toPolyC_nc_k c).combineC_k c ((b.toPolyC_nc_k c).mulConstC_k (Int.negSucc 0) c) = _
    rw [iha, ihb, Poly.mulConstC_k_eq_mulConstC, Poly.combineC_k_eq_combineC]; rfl
  | mul a b iha ihb => show (a.toPolyC_nc_k c).mulC_nc_k (b.toPolyC_nc_k c) c = _; rw [iha, ihb, Poly.mulC_nc_k_eq_mulC_nc]; rfl
  | pow a k ih =>
    simp only [toPolyC_nc.go, cond_eq_ite]
    split
    next h => rw [Nat.beq_eq_true_eq, ← Nat.beq_eq] at h; show Bool.rec (motive := fun _ => Poly) _ _ (k.beq 0) = _; rw [h]
    next h =>
      rw [Nat.beq_eq_true_eq, ← Nat.beq_eq, Bool.not_eq_true] at h
      show Bool.rec (motive := fun _ => Poly) _ _ (k.beq 0) = _
      rw [h]; dsimp only
      show
        (Expr.rec (fun n => .num (Int.emod_k (Int.pow_k n k) (Int.ofNat c)))
          (fun _ => (a.toPolyC_nc_k c).powC_nc_k k c) (fun _ => (a.toPolyC_nc_k c).powC_nc_k k c)
          (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => (a.toPolyC_nc_k c).powC_nc_k k c)
          (fun _ _ _ _ => (a.toPolyC_nc_k c).powC_nc_k k c)
          (fun _ _ _ _ => (a.toPolyC_nc_k c).powC_nc_k k c)
          (fun _ _ _ _ => (a.toPolyC_nc_k c).powC_nc_k k c)
          (fun _ _ _ => (a.toPolyC_nc_k c).powC_nc_k k c)
          a) = match a with
            | .num n => Poly.num ((n ^ k) % c)
            | .var x => Poly.ofMon (Mon.mult { x := x, k := k } Mon.unit)
            | _ => (toPolyC_nc.go c a).powC_nc k c
      cases a <;> simp [*, Int.pow_k_eq, Int.emod_k_eq, Poly.powC_nc_k_eq_powC_nc] <;> rfl

/-!
Theorems for justifying the procedure for commutative rings in `grind`.
-/

open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg
open CommSemiring

theorem denoteInt_eq {α} [Ring α] (k : Int) : denoteInt (α := α) k = k := by
  cases k with
  | ofNat n => show OfNat.ofNat (α := α) n = _; rw [ofNat_eq_natCast, ← intCast_natCast]; rfl
  | negSucc n =>
    show - OfNat.ofNat (α := α) n.succ = _
    rw [ofNat_eq_natCast, ← intCast_natCast, ← Ring.intCast_neg]; rfl

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
  generalize m₁.length + m₂.length + 1 = fuel
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
  unfold combine; generalize p₁.length + p₂.length + 1 = fuel
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

theorem Expr.eq_of_toPoly_eq {α} [CommRing α] (ctx : Context α) (a b : Expr) (h : a.toPoly_k.beq' b.toPoly_k) : a.denote ctx = b.denote ctx := by
  simp only [Poly.beq'_eq, toPoly_k_eq_toPoly] at h
  have h := congrArg (Poly.denote ctx) h
  simp [denote_toPoly] at h
  assumption

theorem Expr.eq_of_toPoly_nc_eq {α} [Ring α] (ctx : Context α) (a b : Expr) (h : a.toPoly_nc_k.beq' b.toPoly_nc_k) : a.denote ctx = b.denote ctx := by
  simp only [Poly.beq'_eq, Expr.toPoly_nc_k_eq_toPoly_nc] at h
  have h := congrArg (Poly.denote ctx) h
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

/-! Kernel-reduction variants of `Mon.degreeOf`, `Mon.cancelVar` and `Poly.cancelVar`. -/

noncomputable def Mon.degreeOf_k (m : Mon) (x : Var) : Nat :=
  Mon.rec 0 (fun pw _ ih => Bool.rec ih pw.k (Nat.beq pw.x x)) m

noncomputable def Mon.cancelVar_k (m : Mon) (x : Var) : Mon :=
  Mon.rec .unit (fun pw m ih => Bool.rec (.mult pw ih) m (Nat.beq pw.x x)) m

@[simp] theorem Mon.degreeOf_k_eq_degreeOf (m : Mon) (x : Var) : Mon.degreeOf_k m x = m.degreeOf x := by
  induction m with
  | unit => rfl
  | mult pw m ih =>
    change Bool.rec (motive := fun _ => Nat) (Mon.degreeOf_k m x) pw.k (Nat.beq pw.x x) = _
    rw [ih]
    simp only [Mon.degreeOf, Bool.rec_eq, cond_eq_ite]
    rfl

@[simp] theorem Mon.cancelVar_k_eq_cancelVar (m : Mon) (x : Var) : Mon.cancelVar_k m x = m.cancelVar x := by
  induction m with
  | unit => rfl
  | mult pw m ih =>
    change Bool.rec (motive := fun _ => Mon) (.mult pw (Mon.cancelVar_k m x)) m (Nat.beq pw.x x) = _
    rw [ih]
    simp only [Mon.cancelVar, Bool.rec_eq, cond_eq_ite]
    rfl

noncomputable def Poly.cancelVar_k (c : Int) (x : Var) (p : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly → Poly) (fun k acc => acc.addConst_k k)
    (fun k m _ ih acc =>
      Bool.rec (ih (acc.insert_k k m))
        (ih (acc.insert_k (Int.ediv_k k (Int.pow_k c (Mon.degreeOf_k m x))) (Mon.cancelVar_k m x)))
        (Nat.blt 0 (Mon.degreeOf_k m x) && Int.beqZero_k (Int.emod_k k (Int.pow_k c (Mon.degreeOf_k m x)))))
    p (.num 0)

theorem Poly.cancelVar_k_eq (c : Int) (x : Var) (p : Poly) : p.cancelVar_k c x = p.cancelVar c x := by
  suffices h : ∀ acc, Poly.rec (motive := fun _ => Poly → Poly) (fun k acc => acc.addConst_k k)
    (fun k m _ ih acc =>
      Bool.rec (ih (acc.insert_k k m))
        (ih (acc.insert_k (Int.ediv_k k (Int.pow_k c (Mon.degreeOf_k m x))) (Mon.cancelVar_k m x)))
        (Nat.blt 0 (Mon.degreeOf_k m x) && Int.beqZero_k (Int.emod_k k (Int.pow_k c (Mon.degreeOf_k m x)))))
    p acc = Poly.cancelVar' c x p acc by exact h (.num 0)
  induction p with
  | num k => intro acc; show acc.addConst_k k = _; rw [Poly.addConst_k_eq_addConst]; rfl
  | add k m p ih =>
    intro acc
    show Bool.rec (motive := fun _ => Poly) _ _ _ = _
    rw [Mon.degreeOf_k_eq_degreeOf, Mon.cancelVar_k_eq_cancelVar, Int.pow_k_eq, Int.emod_k_eq, Int.ediv_k_eq,
      Int.beqZero_k_eq]
    simp only [Poly.cancelVar', cond_eq_ite]
    have hd : (Nat.blt 0 (m.degreeOf x) && (k % c ^ m.degreeOf x == 0)) =
        (decide (m.degreeOf x > 0) && decide (c ^ m.degreeOf x ∣ k)) := by
      cases h₁ : Nat.blt 0 (m.degreeOf x)
      · have : ¬ 0 < m.degreeOf x := by rw [← Nat.blt_eq, h₁]; simp
        simp [this]
      · have : 0 < m.degreeOf x := by rw [← Nat.blt_eq, h₁]
        simp [this, Int.dvd_iff_emod_eq_zero, Bool.beq_eq_decide_eq]
    rw [← hd]
    cases (Nat.blt 0 (m.degreeOf x) && (k % c ^ m.degreeOf x == 0))
    · show Poly.rec (motive := fun _ => Poly → Poly) _ _ p _ = _
      rw [ih, Poly.insert_k_eq_insert]; rfl
    · show Poly.rec (motive := fun _ => Poly → Poly) _ _ p _ = _
      rw [ih, Poly.insert_k_eq_insert]; rfl

noncomputable def cancel_var_cert (c : Int) (x : Var) (p₁ p₂ : Poly) : Bool :=
  Int.bneZero_k c && p₂.beq' (p₁.cancelVar_k c x)

theorem eq_cancel_var {α} [CommRing α] (ctx : Context α) (c : Int) (x : Var) (p₁ p₂ : Poly)
    : cancel_var_cert c x p₁ p₂ → c * x.denote ctx = 1 → p₁.denote ctx = 0 → p₂.denote ctx = 0 := by
  simp [cancel_var_cert, Poly.cancelVar_k_eq]; intros h₁ _ h₂ _; subst p₂
  simp [Poly.denote_cancelVar ctx p₁ c x h₁ h₂]; assumption

theorem diseq_cancel_var {α} [CommRing α] (ctx : Context α) (c : Int) (x : Var) (p₁ p₂ : Poly)
    : cancel_var_cert c x p₁ p₂ → c * x.denote ctx = 1 → p₁.denote ctx ≠ 0 → p₂.denote ctx ≠ 0 := by
  simp [cancel_var_cert, Poly.cancelVar_k_eq]; intros h₁ _ h₂ _; subst p₂
  simp [Poly.denote_cancelVar ctx p₁ c x h₁ h₂]; assumption

theorem le_cancel_var {α} [CommRing α] [LE α] (ctx : Context α) (c : Int) (x : Var) (p₁ p₂ : Poly)
    : cancel_var_cert c x p₁ p₂ → c * x.denote ctx = 1 → p₁.denote ctx ≤ 0 → p₂.denote ctx ≤ 0 := by
  simp [cancel_var_cert, Poly.cancelVar_k_eq]; intros h₁ _ h₂ _; subst p₂
  simp [Poly.denote_cancelVar ctx p₁ c x h₁ h₂]; assumption

theorem lt_cancel_var {α} [CommRing α] [LT α] (ctx : Context α) (c : Int) (x : Var) (p₁ p₂ : Poly)
    : cancel_var_cert c x p₁ p₂ → c * x.denote ctx = 1 → p₁.denote ctx < 0 → p₂.denote ctx < 0 := by
  simp [cancel_var_cert, Poly.cancelVar_k_eq]; intros h₁ _ h₂ _; subst p₂
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
    (h : (a.toPolyC_k c).beq' (b.toPolyC_k c)) : a.denote ctx = b.denote ctx := by
  simp only [Poly.beq'_eq, Expr.toPolyC_k_eq_toPolyC] at h
  have h := congrArg (Poly.denote ctx) h
  simp [denote_toPolyC] at h
  assumption

theorem Expr.eq_of_toPolyC_nc_eq {α c} [Ring α] [IsCharP α c] (ctx : Context α) (a b : Expr)
    (h : (a.toPolyC_nc_k c).beq' (b.toPolyC_nc_k c)) : a.denote ctx = b.denote ctx := by
  simp only [Poly.beq'_eq, Expr.toPolyC_nc_k_eq_toPolyC_nc] at h
  have h := congrArg (Poly.denote ctx) h
  simp [denote_toPolyC_nc] at h
  assumption

/--
`p₁.addEq_k q p` checks `p = p₁.combine q` for sorted `p₁` and `q` in one pass, comparing the head
of `p` with the heads of `p₁` and `q` by equality instead of ordering them.
-/
noncomputable def Poly.addEq_k (p₁ : Poly) : Poly → Poly → Bool :=
  Poly.rec (motive := fun _ => Poly → Poly → Bool)
    (fun k₁ q p => (q.addConst_k k₁).beq' p)
    (fun k₁ m₁ p₁ ih₁ q =>
      Poly.rec (motive := fun _ => Poly → Bool)
        (fun k₂ p => ((Poly.add k₁ m₁ p₁).addConst_k k₂).beq' p)
        (fun k₂ m₂ q ih₂ p =>
          Bool.rec
            (Poly.rec (fun _ => false)
              (fun k m p _ => Bool.rec
                (Bool.rec false (Bool.rec false (ih₂ p) (Int.beq' k k₂)) (Mon.beq' m m₂))
                (Bool.rec false (ih₁ (.add k₂ m₂ q) p) (Int.beq' k k₁))
                (Mon.beq' m m₁)) p)
            (Bool.rec
              (Poly.rec (fun _ => false)
                (fun k m p _ => Bool.rec false (Bool.rec false (ih₁ q p) (Int.beq' k (Int.add_k k₁ k₂))) (Mon.beq' m m₁)) p)
              (ih₁ q p)
              (Int.beqZero_k (Int.add_k k₁ k₂)))
            (Mon.beq' m₁ m₂))
        q)
    p₁

theorem Poly.addEq_k_num (k₁ : Int) (q p : Poly) : (Poly.num k₁).addEq_k q p = (q.addConst_k k₁).beq' p := rfl

theorem Poly.addEq_k_add_num (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (p : Poly) :
    (Poly.add k₁ m₁ p₁).addEq_k (.num k₂) p = ((Poly.add k₁ m₁ p₁).addConst_k k₂).beq' p := rfl

theorem Mon.beq'_eq_beq (m₁ m₂ : Mon) : m₁.beq' m₂ = (m₁ == m₂) := by
  cases h : m₁ == m₂
  · have : m₁ ≠ m₂ := fun e => by simp [e] at h
    rw [← Bool.not_eq_true, Mon.beq'_eq]; exact this
  · rw [Mon.beq'_eq]; exact eq_of_beq h

theorem Poly.addEq_k_add_add_num (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (q : Poly) (k : Int) :
    (Poly.add k₁ m₁ p₁).addEq_k (.add k₂ m₂ q) (.num k) =
      Bool.rec false (Bool.rec false (p₁.addEq_k q (.num k)) (Int.beqZero_k (Int.add_k k₁ k₂))) (Mon.beq' m₁ m₂) := rfl

theorem Poly.addEq_k_add_add_add (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (q : Poly)
    (k : Int) (m : Mon) (p : Poly) :
    (Poly.add k₁ m₁ p₁).addEq_k (.add k₂ m₂ q) (.add k m p) =
      Bool.rec
        (Bool.rec
          (Bool.rec false ((Int.beq' k k₂).and ((Poly.add k₁ m₁ p₁).addEq_k q p)) (Mon.beq' m m₂))
          ((Int.beq' k k₁).and (p₁.addEq_k (.add k₂ m₂ q) p))
          (Mon.beq' m m₁))
        (Bool.rec
          ((Mon.beq' m m₁).and ((Int.beq' k (Int.add_k k₁ k₂)).and (p₁.addEq_k q p)))
          (p₁.addEq_k q (.add k m p))
          (Int.beqZero_k (Int.add_k k₁ k₂)))
        (Mon.beq' m₁ m₂) := rfl

theorem Poly.denote_of_addEq_k {α} [Ring α] (ctx : Context α) (p₁ q p : Poly) (h : p₁.addEq_k q p) :
    p.denote ctx = p₁.denote ctx + q.denote ctx := by
  induction p₁ generalizing q p with
  | num k₁ =>
    rw [addEq_k_num, Poly.beq'_eq, addConst_k_eq_addConst] at h
    rw [← h, denote_addConst, Semiring.add_comm]; rfl
  | add k₁ m₁ p₁ ih₁ =>
    induction q generalizing p with
    | num k₂ =>
      rw [addEq_k_add_num, Poly.beq'_eq, addConst_k_eq_addConst] at h
      rw [← h, denote_addConst]; rfl
    | add k₂ m₂ q ih₂ =>
      have hz : ∀ (k : Int) (p : Poly), Int.beqZero_k (Int.add_k k₁ k₂) = true → p₁.addEq_k q p = true →
          p.denote ctx = (Poly.add k₁ m₁ p₁).denote ctx + (Poly.add k₂ m₂ q).denote ctx → True := fun _ _ _ _ _ => trivial
      clear hz
      cases p with
      | num k =>
        rw [addEq_k_add_add_num] at h
        cases h₁₂ : Mon.beq' m₁ m₂ <;> rw [h₁₂] at h <;> dsimp only at h
        · contradiction
        · rw [Mon.beq'_eq] at h₁₂; subst h₁₂
          cases hk : Int.beqZero_k (Int.add_k k₁ k₂) <;> rw [hk] at h <;> dsimp only at h
          · contradiction
          · rw [Int.beqZero_k_eq, Int.add_k_eq, beq_iff_eq, Int.add_def] at hk
            rw [ih₁ q _ h]; simp only [denote, zsmul_eq_intCast_mul]
            rw [Semiring.add_assoc, add_left_comm (denote ctx p₁), ← Semiring.add_assoc,
              ← right_distrib, ← Ring.intCast_add, hk, Ring.intCast_zero, Semiring.zero_mul, AddCommMonoid.zero_add]
      | add k m p =>
        rw [addEq_k_add_add_add] at h
        cases h₁₂ : Mon.beq' m₁ m₂ <;> rw [h₁₂] at h <;> dsimp only at h
        · cases hm₁ : Mon.beq' m m₁ <;> rw [hm₁] at h <;> dsimp only at h
          · cases hm₂ : Mon.beq' m m₂ <;> rw [hm₂] at h <;> dsimp only at h
            · contradiction
            · rw [Bool.and_eq_true, Int.beq'_eq] at h
              rw [Mon.beq'_eq] at hm₂
              obtain ⟨rfl, h⟩ := h
              have := ih₂ p h
              simp only [denote, zsmul_eq_intCast_mul, hm₂] at this ⊢
              rw [this]; simp only [Semiring.add_assoc, add_left_comm]
          · rw [Bool.and_eq_true, Int.beq'_eq] at h
            rw [Mon.beq'_eq] at hm₁
            obtain ⟨rfl, h⟩ := h
            simp only [denote, zsmul_eq_intCast_mul, hm₁, ih₁ _ p h]
            simp only [Semiring.add_assoc, add_left_comm]
        · rw [Mon.beq'_eq] at h₁₂; subst h₁₂
          cases hk : Int.beqZero_k (Int.add_k k₁ k₂) <;> rw [hk] at h <;> dsimp only at h
          · simp only [Bool.and_eq_true, Int.beq'_eq, Mon.beq'_eq, Int.add_k_eq] at h
            obtain ⟨rfl, rfl, h⟩ := h
            simp only [denote, zsmul_eq_intCast_mul, ih₁ q p h, Int.add_def, Ring.intCast_add, right_distrib]
            simp only [Semiring.add_assoc, add_left_comm]
          · rw [Int.beqZero_k_eq, Int.add_k_eq, beq_iff_eq, Int.add_def] at hk
            rw [ih₁ q _ h]; simp only [denote, zsmul_eq_intCast_mul]
            rw [Semiring.add_assoc, add_left_comm (denote ctx p₁), ← Semiring.add_assoc,
              ← right_distrib, ← Ring.intCast_add, hk, Ring.intCast_zero, Semiring.zero_mul, AddCommMonoid.zero_add]

/--
`p₁.addEqC_k c q p` checks `p = p₁.combineC q c` for sorted `p₁` and `q` in one pass, comparing the head
of `p` with the heads of `p₁` and `q` by equality instead of ordering them.
-/
noncomputable def Poly.addEqC_k (p₁ : Poly) (c : Nat) : Poly → Poly → Bool :=
  Poly.rec (motive := fun _ => Poly → Poly → Bool)
    (fun k₁ q p => (q.addConstC_k k₁ c).beq' p)
    (fun k₁ m₁ p₁ ih₁ q =>
      Poly.rec (motive := fun _ => Poly → Bool)
        (fun k₂ p => ((Poly.add k₁ m₁ p₁).addConstC_k k₂ c).beq' p)
        (fun k₂ m₂ q ih₂ p =>
          Bool.rec
            (Poly.rec (fun _ => false)
              (fun k m p _ => Bool.rec
                (Bool.rec false (Bool.rec false (ih₂ p) (Int.beq' k k₂)) (Mon.beq' m m₂))
                (Bool.rec false (ih₁ (.add k₂ m₂ q) p) (Int.beq' k k₁))
                (Mon.beq' m m₁)) p)
            (Bool.rec
              (Poly.rec (fun _ => false)
                (fun k m p _ => Bool.rec false
                  (Bool.rec false (ih₁ q p) (Int.beq' k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c))))
                  (Mon.beq' m m₁)) p)
              (ih₁ q p)
              (Int.beqZero_k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c))))
            (Mon.beq' m₁ m₂))
        q)
    p₁

theorem Poly.addEqC_k_num (c : Nat) (k₁ : Int) (q p : Poly) : (Poly.num k₁).addEqC_k c q p = (q.addConstC_k k₁ c).beq' p := rfl

theorem Poly.addEqC_k_add_num (c : Nat) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (p : Poly) :
    (Poly.add k₁ m₁ p₁).addEqC_k c (.num k₂) p = ((Poly.add k₁ m₁ p₁).addConstC_k k₂ c).beq' p := rfl

theorem Poly.addEqC_k_add_add_num (c : Nat) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (q : Poly) (k : Int) :
    (Poly.add k₁ m₁ p₁).addEqC_k c (.add k₂ m₂ q) (.num k) =
      Bool.rec false (Bool.rec false (p₁.addEqC_k c q (.num k)) (Int.beqZero_k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c)))) (Mon.beq' m₁ m₂) := rfl

theorem Poly.addEqC_k_add_add_add (c : Nat) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (q : Poly)
    (k : Int) (m : Mon) (p : Poly) :
    (Poly.add k₁ m₁ p₁).addEqC_k c (.add k₂ m₂ q) (.add k m p) =
      Bool.rec
        (Bool.rec
          (Bool.rec false ((Int.beq' k k₂).and ((Poly.add k₁ m₁ p₁).addEqC_k c q p)) (Mon.beq' m m₂))
          ((Int.beq' k k₁).and (p₁.addEqC_k c (.add k₂ m₂ q) p))
          (Mon.beq' m m₁))
        (Bool.rec
          ((Mon.beq' m m₁).and ((Int.beq' k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c))).and (p₁.addEqC_k c q p)))
          (p₁.addEqC_k c q (.add k m p))
          (Int.beqZero_k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c))))
        (Mon.beq' m₁ m₂) := rfl

theorem Poly.denote_of_addEqC_k {α c} [Ring α] [IsCharP α c] (ctx : Context α) (p₁ q p : Poly) (h : p₁.addEqC_k c q p) :
    p.denote ctx = p₁.denote ctx + q.denote ctx := by
  induction p₁ generalizing q p with
  | num k₁ =>
    rw [addEqC_k_num, Poly.beq'_eq, addConstC_k_eq_addConstC] at h
    rw [← h, denote_addConstC, Semiring.add_comm]; rfl
  | add k₁ m₁ p₁ ih₁ =>
    induction q generalizing p with
    | num k₂ =>
      rw [addEqC_k_add_num, Poly.beq'_eq, addConstC_k_eq_addConstC] at h
      rw [← h, denote_addConstC]; rfl
    | add k₂ m₂ q ih₂ =>
      have hz : ∀ (k : Int) (p : Poly), Int.beqZero_k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c)) = true → p₁.addEqC_k c q p = true →
          p.denote ctx = (Poly.add k₁ m₁ p₁).denote ctx + (Poly.add k₂ m₂ q).denote ctx → True := fun _ _ _ _ _ => trivial
      clear hz
      cases p with
      | num k =>
        rw [addEqC_k_add_add_num] at h
        cases h₁₂ : Mon.beq' m₁ m₂ <;> rw [h₁₂] at h <;> dsimp only at h
        · contradiction
        · rw [Mon.beq'_eq] at h₁₂; subst h₁₂
          cases hk : Int.beqZero_k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c)) <;> rw [hk] at h <;> dsimp only at h
          · contradiction
          · rw [Int.beqZero_k_eq, Int.emod_k_eq, Int.add_k_eq, beq_iff_eq, Int.add_def, Int.ofNat_eq_natCast] at hk
            rw [ih₁ q _ h]; simp only [denote, zsmul_eq_intCast_mul]
            rw [Semiring.add_assoc, add_left_comm (denote ctx p₁), ← Semiring.add_assoc,
              ← right_distrib, ← Ring.intCast_add, ← IsCharP.intCast_emod (p := c), hk, Ring.intCast_zero, Semiring.zero_mul, AddCommMonoid.zero_add]
      | add k m p =>
        rw [addEqC_k_add_add_add] at h
        cases h₁₂ : Mon.beq' m₁ m₂ <;> rw [h₁₂] at h <;> dsimp only at h
        · cases hm₁ : Mon.beq' m m₁ <;> rw [hm₁] at h <;> dsimp only at h
          · cases hm₂ : Mon.beq' m m₂ <;> rw [hm₂] at h <;> dsimp only at h
            · contradiction
            · rw [Bool.and_eq_true, Int.beq'_eq] at h
              rw [Mon.beq'_eq] at hm₂
              obtain ⟨rfl, h⟩ := h
              have := ih₂ p h
              simp only [denote, zsmul_eq_intCast_mul, hm₂] at this ⊢
              rw [this]; simp only [Semiring.add_assoc, add_left_comm]
          · rw [Bool.and_eq_true, Int.beq'_eq] at h
            rw [Mon.beq'_eq] at hm₁
            obtain ⟨rfl, h⟩ := h
            simp only [denote, zsmul_eq_intCast_mul, hm₁, ih₁ _ p h]
            simp only [Semiring.add_assoc, add_left_comm]
        · rw [Mon.beq'_eq] at h₁₂; subst h₁₂
          cases hk : Int.beqZero_k (Int.emod_k (Int.add_k k₁ k₂) (Int.ofNat c)) <;> rw [hk] at h <;> dsimp only at h
          · simp only [Bool.and_eq_true, Int.beq'_eq, Mon.beq'_eq, Int.add_k_eq, Int.emod_k_eq] at h
            obtain ⟨rfl, rfl, h⟩ := h
            simp only [denote, zsmul_eq_intCast_mul, ih₁ q p h, Int.add_def, Int.ofNat_eq_natCast, IsCharP.intCast_emod, Ring.intCast_add, right_distrib]
            simp only [Semiring.add_assoc, add_left_comm]
          · rw [Int.beqZero_k_eq, Int.emod_k_eq, Int.add_k_eq, beq_iff_eq, Int.add_def, Int.ofNat_eq_natCast] at hk
            rw [ih₁ q _ h]; simp only [denote, zsmul_eq_intCast_mul]
            rw [Semiring.add_assoc, add_left_comm (denote ctx p₁), ← Semiring.add_assoc,
              ← right_distrib, ← Ring.intCast_add, ← IsCharP.intCast_emod (p := c), hk, Ring.intCast_zero, Semiring.zero_mul, AddCommMonoid.zero_add]

/-! `Expr` spelling of a polynomial: the left-associated sum of its terms, as in `Poly.denote'`. -/

def Power.toExpr (pw : Power) : Expr :=
  if pw.k == 1 then
    .var pw.x
  else
    .pow (.var pw.x) pw.k

def Mon.toExpr (m : Mon) : Expr :=
  match m with
  | .unit => .num 1
  | .mult pw m => go m pw.toExpr
where
  go (m : Mon) (acc : Expr) : Expr :=
    match m with
    | .unit => acc
    | .mult pw m => go m (.mul acc pw.toExpr)

def Poly.toExpr (p : Poly) : Expr :=
  match p with
  | .num k => .num k
  | .add k m p => go p (goTerm k m)
where
  goTerm (k : Int) (m : Mon) : Expr :=
    if k == 1 then
      m.toExpr
    else
      .mul (.num k) m.toExpr

  go (p : Poly) (acc : Expr) : Expr :=
    match p with
    | .num k => bif k == 0 then acc else .add acc (.num k)
    | .add k m p => go p (.add acc (goTerm k m))

noncomputable def Power.toExpr_k (pw : Power) : Expr :=
  Bool.rec (.pow (.var pw.x) pw.k) (.var pw.x) (Nat.beq pw.k 1)

noncomputable def Mon.toExpr_k.go (m : Mon) : Expr → Expr :=
  Mon.rec (fun acc => acc) (fun pw _ ih acc => ih (.mul acc pw.toExpr_k)) m

noncomputable def Mon.toExpr_k (m : Mon) : Expr :=
  Mon.rec (.num 1) (fun pw m _ => Mon.toExpr_k.go m pw.toExpr_k) m

noncomputable def Poly.toExpr_k.goTerm (k : Int) (m : Mon) : Expr :=
  Bool.rec (.mul (.num k) m.toExpr_k) m.toExpr_k (Int.beq' k 1)

noncomputable def Poly.toExpr_k.go (p : Poly) : Expr → Expr :=
  Poly.rec (fun k acc => Bool.rec (.add acc (.num k)) acc (Int.beqZero_k k))
    (fun k m _ ih acc => ih (.add acc (Poly.toExpr_k.goTerm k m))) p

noncomputable def Poly.toExpr_k (p : Poly) : Expr :=
  Poly.rec (fun k => .num k) (fun k m p _ => Poly.toExpr_k.go p (Poly.toExpr_k.goTerm k m)) p

@[simp] theorem Power.toExpr_k_eq (pw : Power) : pw.toExpr_k = pw.toExpr := by
  unfold toExpr_k toExpr
  rw [show Nat.beq pw.k 1 = (pw.k == 1) from rfl]
  cases pw.k == 1 <;> rfl

theorem Mon.toExpr_k_go_eq (m : Mon) (acc : Expr) : Mon.toExpr_k.go m acc = Mon.toExpr.go m acc := by
  induction m generalizing acc with
  | unit => rfl
  | mult pw m ih => show Mon.toExpr_k.go m (.mul acc pw.toExpr_k) = _; rw [ih, Power.toExpr_k_eq]; rfl

@[simp] theorem Mon.toExpr_k_eq (m : Mon) : m.toExpr_k = m.toExpr := by
  cases m with
  | unit => rfl
  | mult pw m => show Mon.toExpr_k.go m pw.toExpr_k = _; rw [Mon.toExpr_k_go_eq, Power.toExpr_k_eq]; rfl

theorem Poly.toExpr_k_goTerm_eq (k : Int) (m : Mon) : Poly.toExpr_k.goTerm k m = Poly.toExpr.goTerm k m := by
  unfold toExpr_k.goTerm toExpr.goTerm; rw [Mon.toExpr_k_eq]
  by_cases h : k = 1
  · subst h; rfl
  · have h' : Int.beq' k 1 = false := by simpa using h
    rw [h']; simp [h]

theorem Poly.toExpr_k_go_eq (p : Poly) (acc : Expr) : Poly.toExpr_k.go p acc = Poly.toExpr.go p acc := by
  induction p generalizing acc with
  | num k =>
    show Bool.rec (motive := fun _ => Expr) (.add acc (.num k)) acc (Int.beqZero_k k) =
      bif k == 0 then acc else .add acc (.num k)
    rw [Int.beqZero_k_eq]; cases k == 0 <;> rfl
  | add k m p ih =>
    show Poly.toExpr_k.go p (.add acc (Poly.toExpr_k.goTerm k m)) = _
    rw [ih, Poly.toExpr_k_goTerm_eq]; rfl

@[simp] theorem Poly.toExpr_k_eq (p : Poly) : p.toExpr_k = p.toExpr := by
  cases p with
  | num k => rfl
  | add k m p => show Poly.toExpr_k.go p (Poly.toExpr_k.goTerm k m) = _; rw [Poly.toExpr_k_go_eq, Poly.toExpr_k_goTerm_eq]; rfl

theorem Power.denote_toExpr {α} [Ring α] (ctx : Context α) (pw : Power) : pw.toExpr.denote ctx = pw.denote ctx := by
  unfold toExpr; split
  · next h => simp at h; cases pw; simp at h; subst h; rfl
  · next h => cases pw with
    | mk x k => show (x.denote ctx) ^ k = _; simp [Power.denote_eq]

theorem Mon.denote_toExpr_go {α} [Ring α] (ctx : Context α) (m : Mon) (acc : Expr) :
    (Mon.toExpr.go m acc).denote ctx = acc.denote ctx * m.denote ctx := by
  induction m generalizing acc with
  | unit => simp [toExpr.go, Mon.denote, Semiring.mul_one]
  | mult pw m ih =>
    simp only [toExpr.go, ih]
    show acc.denote ctx * pw.toExpr.denote ctx * m.denote ctx = _
    rw [Power.denote_toExpr, Semiring.mul_assoc]; rfl

theorem Mon.denote_toExpr {α} [Ring α] (ctx : Context α) (m : Mon) : m.toExpr.denote ctx = m.denote ctx := by
  cases m with
  | unit => simp [toExpr, Expr.denote, denoteInt_eq, Ring.intCast_one]; rfl
  | mult pw m => simp only [toExpr, denote_toExpr_go, Power.denote_toExpr]; rfl

theorem Poly.denote_toExpr_goTerm {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) :
    (Poly.toExpr.goTerm k m).denote ctx = k • m.denote ctx := by
  unfold toExpr.goTerm; split
  · next h => simp at h; subst h; rw [Mon.denote_toExpr, zsmul_eq_intCast_mul, Ring.intCast_one, Semiring.one_mul]
  · show denoteInt k * m.toExpr.denote ctx = _
    rw [Mon.denote_toExpr, denoteInt_eq, zsmul_eq_intCast_mul]

theorem Poly.denote_toExpr_go {α} [Ring α] (ctx : Context α) (p : Poly) (acc : Expr) :
    (Poly.toExpr.go p acc).denote ctx = acc.denote ctx + p.denote ctx := by
  induction p generalizing acc with
  | num k =>
    show (bif k == 0 then acc else .add acc (.num k)).denote ctx = acc.denote ctx + (k : α)
    by_cases h : k = 0
    · subst h; rw [show ((0 : Int) == 0) = true from rfl, Ring.intCast_zero, Semiring.add_zero]; rfl
    · rw [show (k == 0) = false by simpa using h]
      show acc.denote ctx + denoteInt k = _; rw [denoteInt_eq]
  | add k m p ih =>
    simp only [toExpr.go, ih]
    show acc.denote ctx + (Poly.toExpr.goTerm k m).denote ctx + p.denote ctx = _
    rw [Poly.denote_toExpr_goTerm, Semiring.add_assoc]; rfl

theorem Poly.denote_toExpr {α} [Ring α] (ctx : Context α) (p : Poly) : p.toExpr.denote ctx = p.denote ctx := by
  cases p with
  | num k => show denoteInt k = _; rw [denoteInt_eq]; rfl
  | add k m p => simp only [toExpr, denote_toExpr_go, denote_toExpr_goTerm]; rfl

theorem Expr.eq_of_toPoly_eq_toExpr {α} [CommRing α] (ctx : Context α) (a b : Expr) (p : Poly)
    (h₁ : p = a.toPoly_k) (h₂ : b = p.toExpr_k) : a.denote ctx = b.denote ctx := by
  subst h₁ h₂; rw [Poly.toExpr_k_eq, Poly.denote_toExpr, Expr.toPoly_k_eq_toPoly, Expr.denote_toPoly]


/-!
Balanced polynomial normalization for certificates. `Expr.toPolyB_k` collects the summands of
sums and differences into a list and adds them pairwise, level by level, and so does
`Poly.mulB_k` with the partial products of a multiplication. The kernel then checks a sum of `n`
summands with `O(n log n)` monomial comparisons, instead of the `O(n²)` of adding them one by one
with `Expr.toPoly_k` when each summand goes at the end of the polynomial. The result is the
same polynomial as `Expr.toPoly`, because `Poly.combine` of polynomials in normal form is their
normal form.
-/

/-- The sum of the denotations of `ps`. -/
def Poly.denoteList {α} [Ring α] (ctx : Context α) : List Poly → α
  | [] => 0
  | p :: ps => p.denote ctx + denoteList ctx ps

/-- One level of pairwise additions with `f`, with `pend` the pending first summand of a pair. -/
noncomputable def Poly.pairs_k (f : Poly → Poly → Poly) (ps : List Poly) : Option Poly → List Poly :=
  List.rec (motive := fun _ => Option Poly → List Poly)
    (fun pend => Option.rec [] (fun p => [p]) pend)
    (fun a _ ih pend => Option.rec (ih (some a)) (fun p => f p a :: ih none) pend)
    ps

/-- Adds `ps` with `f` from the right. -/
noncomputable def Poly.foldr_k (f : Poly → Poly → Poly) (ps : List Poly) : Poly :=
  List.rec (.num 0) (fun a _ ih => f a ih) ps

/--
Adds `ps` with `f` by levels of pairwise additions. Each level consumes an element of `fuel`;
the list of summands is at most halved by each level, so `ps` itself is enough fuel.
-/
noncomputable def Poly.sumGo_k (f : Poly → Poly → Poly) (fuel : List Poly) : List Poly → Poly :=
  List.rec (motive := fun _ => List Poly → Poly)
    (fun ps => foldr_k f ps)
    (fun _ _ ih ps => List.rec (.num 0) (fun a rest _ => List.rec a (fun _ _ _ => ih (pairs_k f ps none)) rest) ps)
    fuel

noncomputable def Poly.sumB_k (f : Poly → Poly → Poly) (ps : List Poly) : Poly :=
  sumGo_k f ps ps

/-- The partial products of `p₁ * p₂`, one per monomial of `p₁`. -/
noncomputable def Poly.mulTerms_k (p₁ p₂ : Poly) : List Poly :=
  Poly.rec (fun k => [p₂.mulConst_k k]) (fun k m _ ih => p₂.mulMon_k k m :: ih) p₁

/-- `true` if `p` is a monomial `k * m` without constant. -/
noncomputable def Poly.isMon_k (p : Poly) : Bool :=
  Poly.rec (fun _ => false) (fun _ _ q _ => Poly.rec (fun c => Int.beqZero_k c) (fun _ _ _ _ => false) q) p

/-- `q` multiplied by the first monomial of `p`. -/
noncomputable def Poly.mulByMon_k (p q : Poly) : Poly :=
  Poly.rec (fun _ => .num 0) (fun k m _ _ => q.mulMon_k k m) p

/--
`p₁ * p₂`, adding the partial products pairwise unless a factor is a constant or a monomial.
-/
noncomputable def Poly.mulB_k (p₁ p₂ : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly) (fun k => p₂.mulConst_k k)
    (fun _ _ _ _ => Poly.rec (motive := fun _ => Poly) (fun k => p₁.mulConst_k k)
      (fun _ _ _ _ =>
        Bool.rec (Bool.rec (sumB_k combine_k (mulTerms_k p₁ p₂)) (p₂.mulByMon_k p₁) p₂.isMon_k)
          (p₁.mulByMon_k p₂) p₁.isMon_k)
      p₂)
    p₁

noncomputable def Poly.powB_k (p : Poly) (k : Nat) : Poly :=
  Nat.rec (.num 1) (fun k ih => Bool.rec (p.mulB_k ih) p (Nat.beq k 0)) k

/-- The polynomial of `a ^ k`, where `p` is the polynomial of `a`. -/
noncomputable def Expr.powLeafB_k (a : Expr) (k : Nat) (p : Poly) : Poly :=
  Bool.rec
    (Expr.rec (fun n => .num (Int.pow_k n k)) (fun n => .num (Int.ofNat (Nat.pow n k))) (fun n => .num (Int.pow_k n k))
      (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ => p.powB_k k)
      a)
    (.num 1)
    (k.beq 0)

/-- `p`, negated if `s`. -/
noncomputable def Poly.signB_k (p : Poly) (s : Bool) : Poly :=
  Bool.rec p (p.mulConst_k (Int.negSucc 0)) s

/--
`e.sumsB_k s acc` prepends to `acc` the polynomials of the summands of `e`, negated if `s`.
The summands are the maximal subterms of `e` that are not sums, differences or negations.
-/
noncomputable def Expr.sumsB_k (e : Expr) : Bool → List Poly → List Poly :=
  Expr.rec
    (fun k s acc => (Poly.num k).signB_k s :: acc)
    (fun k s acc => (Poly.num k).signB_k s :: acc)
    (fun k s acc => (Poly.num k).signB_k s :: acc)
    (fun x s acc => (Poly.ofVar x).signB_k s :: acc)
    (fun _ ih s acc => ih (Bool.rec true false s) acc)
    (fun _ _ ih₁ ih₂ s acc => ih₁ s (ih₂ s acc))
    (fun _ _ ih₁ ih₂ s acc => ih₁ s (ih₂ (Bool.rec true false s) acc))
    (fun _ _ ih₁ ih₂ s acc => ((Poly.sumB_k Poly.combine_k (ih₁ false [])).mulB_k (Poly.sumB_k Poly.combine_k (ih₂ false []))).signB_k s :: acc)
    (fun a k ih s acc => (a.powLeafB_k k (Poly.sumB_k Poly.combine_k (ih false []))).signB_k s :: acc)
    e

noncomputable def Expr.toPolyB_k (e : Expr) : Poly :=
  Poly.sumB_k Poly.combine_k (e.sumsB_k false [])

/--
`Expr.toPolyB_k` if `bal`, and `Expr.toPoly_k` otherwise. The balanced additions cost more
kernel steps for short sums, so the certificate producer chooses.
-/
noncomputable def Expr.toPolyX_k (bal : Bool) (e : Expr) : Poly :=
  Bool.rec e.toPoly_k e.toPolyB_k bal

section
variable {α} [CommRing α] (ctx : Context α)

theorem Poly.denoteList_pairs_k (f : Poly → Poly → Poly) (hf : ∀ a b, (f a b).denote ctx = a.denote ctx + b.denote ctx)
    (ps : List Poly) (pend : Option Poly) :
    denoteList ctx (pairs_k f ps pend) = (Option.rec 0 (fun p => p.denote ctx) pend : α) + denoteList ctx ps := by
  induction ps generalizing pend with
  | nil => cases pend <;> simp [pairs_k, denoteList, add_zero]
  | cons a ps ih =>
    cases pend with
    | none => show denoteList ctx (pairs_k f ps (some a)) = _; rw [ih]; simp [denoteList, zero_add]
    | some p =>
      show (f p a).denote ctx + denoteList ctx (pairs_k f ps none) = _
      rw [ih, hf]; simp [denoteList, zero_add, add_assoc]

theorem Poly.denote_foldr_k (f : Poly → Poly → Poly) (hf : ∀ a b, (f a b).denote ctx = a.denote ctx + b.denote ctx)
    (ps : List Poly) : (foldr_k f ps).denote ctx = denoteList ctx ps := by
  induction ps with
  | nil => show ((0 : Int) : α) = 0; rw [intCast_zero]
  | cons a ps ih => show (f a (foldr_k f ps)).denote ctx = _; rw [hf, ih]; rfl

theorem Poly.denote_sumGo_k (f : Poly → Poly → Poly) (hf : ∀ a b, (f a b).denote ctx = a.denote ctx + b.denote ctx)
    (fuel ps : List Poly) : (sumGo_k f fuel ps).denote ctx = denoteList ctx ps := by
  induction fuel generalizing ps with
  | nil => exact denote_foldr_k ctx f hf ps
  | cons _ fuel ih =>
    match ps with
    | [] => show ((0 : Int) : α) = 0; rw [intCast_zero]
    | [a] => show a.denote ctx = a.denote ctx + 0; rw [add_zero]
    | a :: b :: ps =>
      show (sumGo_k f fuel (pairs_k f (a :: b :: ps) none)).denote ctx = _
      rw [ih, denoteList_pairs_k ctx f hf]; simp [zero_add]

theorem Poly.denote_sumB_k (f : Poly → Poly → Poly) (hf : ∀ a b, (f a b).denote ctx = a.denote ctx + b.denote ctx)
    (ps : List Poly) : (sumB_k f ps).denote ctx = denoteList ctx ps :=
  denote_sumGo_k ctx f hf ps ps

theorem Poly.denote_combine_k (a b : Poly) : (combine_k a b).denote ctx = a.denote ctx + b.denote ctx := by
  rw [combine_k_eq_combine, denote_combine]

theorem Poly.denoteList_mulTerms_k (p₁ p₂ : Poly) : denoteList ctx (mulTerms_k p₁ p₂) = p₁.denote ctx * p₂.denote ctx := by
  induction p₁ with
  | num k => show (p₂.mulConst_k k).denote ctx + 0 = _; rw [add_zero, mulConst_k_eq_mulConst, denote_mulConst]; rfl
  | add k m p ih =>
    show (p₂.mulMon_k k m).denote ctx + denoteList ctx (mulTerms_k p p₂) = _
    rw [ih, mulMon_k_eq_mulMon, denote_mulMon]; simp [denote, zsmul_eq_intCast_mul, right_distrib]

theorem Poly.eq_of_isMon_k {p : Poly} (h : p.isMon_k = true) : ∃ k m, p = .add k m (.num 0) := by
  cases p with
  | num => cases h
  | add k m q =>
    cases q with
    | num c =>
      have : Int.beqZero_k c = true := h
      rw [Int.beqZero_k_eq] at this; simp at this; subst this; exact ⟨k, m, rfl⟩
    | add => cases h

theorem Poly.denote_mulByMon_k {p : Poly} (q : Poly) (h : p.isMon_k = true) :
    (p.mulByMon_k q).denote ctx = p.denote ctx * q.denote ctx := by
  have ⟨k, m, hp⟩ := eq_of_isMon_k h; subst hp
  show (q.mulMon_k k m).denote ctx = _
  rw [mulMon_k_eq_mulMon, denote_mulMon]; simp [denote, zsmul_eq_intCast_mul, intCast_zero, add_zero]

theorem Poly.denote_mulB_k (p₁ p₂ : Poly) : (mulB_k p₁ p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  cases p₁ with
  | num k => show (p₂.mulConst_k k).denote ctx = _; rw [mulConst_k_eq_mulConst, denote_mulConst]; rfl
  | add k₁ m₁ q₁ =>
    cases p₂ with
    | num k =>
      show ((Poly.add k₁ m₁ q₁).mulConst_k k).denote ctx = _
      rw [mulConst_k_eq_mulConst, denote_mulConst, mul_comm]; rfl
    | add k₂ m₂ q₂ =>
      show (Bool.rec (Bool.rec _ _ (Poly.add k₂ m₂ q₂).isMon_k) _ (Poly.add k₁ m₁ q₁).isMon_k : Poly).denote ctx = _
      cases h₁ : (Poly.add k₁ m₁ q₁).isMon_k
      · cases h₂ : (Poly.add k₂ m₂ q₂).isMon_k
        · show (sumB_k combine_k (mulTerms_k _ _)).denote ctx = _
          rw [denote_sumB_k ctx _ (denote_combine_k ctx), denoteList_mulTerms_k]
        · show ((Poly.add k₂ m₂ q₂).mulByMon_k _).denote ctx = _
          rw [denote_mulByMon_k ctx _ h₂, mul_comm]
      · exact denote_mulByMon_k ctx _ h₁

theorem Poly.denote_powB_k (p : Poly) (k : Nat) : (powB_k p k).denote ctx = p.denote ctx ^ k := by
  induction k with
  | zero => show ((1 : Int) : α) = _; rw [intCast_one, pow_zero]
  | succ k ih =>
    cases k with
    | zero => show p.denote ctx = _; rw [pow_succ, pow_zero, one_mul]
    | succ k =>
      show (p.mulB_k (powB_k p (k + 1))).denote ctx = _
      rw [denote_mulB_k, ih, pow_succ (n := k + 1), mul_comm]

theorem Expr.denote_powLeafB_k (a : Expr) (k : Nat) (p : Poly) (h : p.denote ctx = a.denote ctx) :
    (a.powLeafB_k k p).denote ctx = a.denote ctx ^ k := by
  unfold powLeafB_k
  cases hk : k.beq 0
  · have hk : k ≠ 0 := Nat.ne_of_beq_eq_false hk
    dsimp only
    cases a <;> simp [Expr.denote, Poly.denote_powB_k, h, Poly.denote, Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one, intCast_pow, denoteInt_eq, Ring.intCast_natCast, Semiring.natCast_pow]
  · have hk : k = 0 := Nat.eq_of_beq_eq_true hk
    subst hk; show ((1 : Int) : α) = _; rw [intCast_one, pow_zero]

theorem Poly.denote_signB_k (p : Poly) (s : Bool) : (p.signB_k s).denote ctx = bif s then -p.denote ctx else p.denote ctx := by
  cases s
  · rfl
  · show (p.mulConst_k (Int.negSucc 0)).denote ctx = _
    rw [mulConst_k_eq_mulConst, denote_mulConst]; simp [intCast_neg, neg_mul, intCast_one, one_mul]

theorem Expr.denoteList_sumsB_k (e : Expr) (s : Bool) (acc : List Poly) :
    Poly.denoteList ctx (e.sumsB_k s acc) = (bif s then -e.denote ctx else e.denote ctx) + Poly.denoteList ctx acc := by
  have hB (a : Expr) (ih : ∀ s acc, Poly.denoteList ctx (a.sumsB_k s acc) = (bif s then -a.denote ctx else a.denote ctx) + Poly.denoteList ctx acc) :
      (Poly.sumB_k Poly.combine_k (a.sumsB_k false [])).denote ctx = a.denote ctx := by
    rw [Poly.denote_sumB_k ctx _ (Poly.denote_combine_k ctx), ih]; simp [Poly.denoteList, add_zero]
  induction e generalizing s acc with
  | num k => show Poly.denote ctx (Poly.signB_k (Poly.num k) s) + _ = _; rw [Poly.denote_signB_k]; simp [Expr.denote, Poly.denote, denoteInt_eq]
  | natCast k => show Poly.denote ctx (Poly.signB_k (Poly.num k) s) + _ = _; rw [Poly.denote_signB_k]; simp [Expr.denote, Poly.denote, Ring.intCast_natCast]
  | intCast k => show Poly.denote ctx (Poly.signB_k (Poly.num k) s) + _ = _; rw [Poly.denote_signB_k]; simp [Expr.denote, Poly.denote]
  | var x => show Poly.denote ctx (Poly.signB_k (Poly.ofVar x) s) + _ = _; rw [Poly.denote_signB_k, Poly.denote_ofVar]; rfl
  | neg a ih =>
    show Poly.denoteList ctx (a.sumsB_k (Bool.rec true false s) acc) = _
    rw [ih]; cases s <;> simp [Expr.denote, neg_neg]
  | add a b iha ihb =>
    show Poly.denoteList ctx (a.sumsB_k s (b.sumsB_k s acc)) = _
    rw [iha, ihb]; cases s <;> simp [Expr.denote, neg_add, add_assoc]
  | sub a b iha ihb =>
    show Poly.denoteList ctx (a.sumsB_k s (b.sumsB_k (Bool.rec true false s) acc)) = _
    rw [iha, ihb]; cases s <;> simp [Expr.denote, sub_eq_add_neg, neg_add, neg_neg, add_assoc]
  | mul a b iha ihb =>
    show (((Poly.sumB_k Poly.combine_k (a.sumsB_k false [])).mulB_k
      (Poly.sumB_k Poly.combine_k (b.sumsB_k false []))).signB_k s).denote ctx + Poly.denoteList ctx acc = _
    rw [Poly.denote_signB_k, Poly.denote_mulB_k, hB a iha, hB b ihb]; rfl
  | pow a k ih =>
    show ((a.powLeafB_k k (Poly.sumB_k Poly.combine_k (a.sumsB_k false []))).signB_k s).denote ctx + Poly.denoteList ctx acc = _
    rw [Poly.denote_signB_k, Expr.denote_powLeafB_k ctx a k _ (hB a ih)]; rfl

theorem Expr.denote_toPolyB_k (e : Expr) : e.toPolyB_k.denote ctx = e.denote ctx := by
  rw [toPolyB_k, Poly.denote_sumB_k ctx _ (Poly.denote_combine_k ctx), denoteList_sumsB_k]
  simp [Poly.denoteList, add_zero]

end

theorem Expr.denote_toPolyX_k {α} [CommRing α] (ctx : Context α) (bal : Bool) (e : Expr) :
    (e.toPolyX_k bal).denote ctx = e.denote ctx := by
  cases bal
  · show e.toPoly_k.denote ctx = _; rw [toPoly_k_eq_toPoly, denote_toPoly]
  · exact denote_toPolyB_k ctx e

theorem Expr.eq_of_toPolyX_eq_toExpr {α} [CommRing α] (ctx : Context α) (bal : Bool) (a b : Expr) (p : Poly)
    (h₁ : p = a.toPolyX_k bal) (h₂ : b = p.toExpr_k) : a.denote ctx = b.denote ctx := by
  subst h₁ h₂; rw [Poly.toExpr_k_eq, Poly.denote_toExpr, Expr.denote_toPolyX_k]

/-! Balanced polynomial normalization in a ring of characteristic `c`, like `Expr.toPolyB_k`. -/

noncomputable def Poly.mulTermsC_k (p₁ p₂ : Poly) (c : Nat) : List Poly :=
  Poly.rec (fun k => [p₂.mulConstC_k k c]) (fun k m _ ih => p₂.mulMonC_k k m c :: ih) p₁

/-- `q` multiplied by the first monomial of `p` in characteristic `c`. -/
noncomputable def Poly.mulByMonC_k (p q : Poly) (c : Nat) : Poly :=
  Poly.rec (fun _ => .num 0) (fun k m _ _ => q.mulMonC_k k m c) p

/-- `Poly.mulB_k` in characteristic `c`. -/
noncomputable def Poly.mulBC_k (p₁ p₂ : Poly) (c : Nat) : Poly :=
  Poly.rec (motive := fun _ => Poly) (fun k => p₂.mulConstC_k k c)
    (fun _ _ _ _ => Poly.rec (motive := fun _ => Poly) (fun k => p₁.mulConstC_k k c)
      (fun _ _ _ _ =>
        Bool.rec (Bool.rec (sumB_k (fun a b => a.combineC_k c b) (mulTermsC_k p₁ p₂ c)) (p₂.mulByMonC_k p₁ c) p₂.isMon_k)
          (p₁.mulByMonC_k p₂ c) p₁.isMon_k)
      p₂)
    p₁

noncomputable def Poly.powBC_k (p : Poly) (k : Nat) (c : Nat) : Poly :=
  Nat.rec (.num 1) (fun k ih => Bool.rec (p.mulBC_k ih c) p (Nat.beq k 0)) k

/-- The polynomial of `a ^ k` in characteristic `c`, where `p` is the polynomial of `a`. -/
noncomputable def Expr.powLeafBC_k (a : Expr) (k : Nat) (c : Nat) (p : Poly) : Poly :=
  Bool.rec
    (Expr.rec (fun n => .num (Int.emod_k (Int.pow_k n k) (Int.ofNat c)))
      (fun _ => p.powBC_k k c) (fun _ => p.powBC_k k c)
      (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => p.powBC_k k c)
      (fun _ _ _ _ => p.powBC_k k c)
      (fun _ _ _ _ => p.powBC_k k c)
      (fun _ _ _ _ => p.powBC_k k c)
      (fun _ _ _ => p.powBC_k k c)
      a)
    (.num 1)
    (k.beq 0)

/-- `p`, negated in characteristic `c` if `s`. -/
noncomputable def Poly.signBC_k (p : Poly) (c : Nat) (s : Bool) : Poly :=
  Bool.rec p (p.mulConstC_k (Int.negSucc 0) c) s

/-- `Expr.sumsB_k` in characteristic `c`. -/
noncomputable def Expr.sumsBC_k (e : Expr) (c : Nat) : Bool → List Poly → List Poly :=
  Expr.rec
    (fun k s acc => (Poly.num (Int.emod_k k (Int.ofNat c))).signBC_k c s :: acc)
    (fun k s acc => (Poly.num (Int.emod_k (Int.ofNat k) (Int.ofNat c))).signBC_k c s :: acc)
    (fun k s acc => (Poly.num (Int.emod_k k (Int.ofNat c))).signBC_k c s :: acc)
    (fun x s acc => (Poly.ofVar x).signBC_k c s :: acc)
    (fun _ ih s acc => ih (Bool.rec true false s) acc)
    (fun _ _ ih₁ ih₂ s acc => ih₁ s (ih₂ s acc))
    (fun _ _ ih₁ ih₂ s acc => ih₁ s (ih₂ (Bool.rec true false s) acc))
    (fun _ _ ih₁ ih₂ s acc =>
      ((Poly.sumB_k (fun a b => a.combineC_k c b) (ih₁ false [])).mulBC_k
        (Poly.sumB_k (fun a b => a.combineC_k c b) (ih₂ false [])) c).signBC_k c s :: acc)
    (fun a k ih s acc => (a.powLeafBC_k k c (Poly.sumB_k (fun a b => a.combineC_k c b) (ih false []))).signBC_k c s :: acc)
    e

noncomputable def Expr.toPolyBC_k (e : Expr) (c : Nat) : Poly :=
  Poly.sumB_k (fun a b => a.combineC_k c b) (e.sumsBC_k c false [])

/-- `Expr.toPolyBC_k` if `bal`, and `Expr.toPolyC_k` otherwise. -/
noncomputable def Expr.toPolyXC_k (bal : Bool) (e : Expr) (c : Nat) : Poly :=
  Bool.rec (e.toPolyC_k c) (e.toPolyBC_k c) bal

section
variable {α c} [CommRing α] [IsCharP α c] (ctx : Context α)

theorem Poly.denote_combineC_k (a b : Poly) : (a.combineC_k c b).denote ctx = a.denote ctx + b.denote ctx := by
  rw [combineC_k_eq_combineC, denote_combineC]

theorem Poly.denoteList_mulTermsC_k (p₁ p₂ : Poly) : denoteList ctx (mulTermsC_k p₁ p₂ c) = p₁.denote ctx * p₂.denote ctx := by
  induction p₁ with
  | num k => show (p₂.mulConstC_k k c).denote ctx + 0 = _; rw [add_zero, mulConstC_k_eq_mulConstC, denote_mulConstC]; rfl
  | add k m p ih =>
    show (p₂.mulMonC_k k m c).denote ctx + denoteList ctx (mulTermsC_k p p₂ c) = _
    rw [ih, mulMonC_k_eq_mulMonC, denote_mulMonC]; simp [denote, zsmul_eq_intCast_mul, right_distrib]

theorem Poly.denote_mulByMonC_k {p : Poly} (q : Poly) (h : p.isMon_k = true) :
    (p.mulByMonC_k q c).denote ctx = p.denote ctx * q.denote ctx := by
  have ⟨k, m, hp⟩ := eq_of_isMon_k h; subst hp
  show (q.mulMonC_k k m c).denote ctx = _
  rw [mulMonC_k_eq_mulMonC, denote_mulMonC]; simp [denote, zsmul_eq_intCast_mul, intCast_zero, add_zero]

theorem Poly.denote_mulBC_k (p₁ p₂ : Poly) : (mulBC_k p₁ p₂ c).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  cases p₁ with
  | num k => show (p₂.mulConstC_k k c).denote ctx = _; rw [mulConstC_k_eq_mulConstC, denote_mulConstC]; rfl
  | add k₁ m₁ q₁ =>
    cases p₂ with
    | num k =>
      show ((Poly.add k₁ m₁ q₁).mulConstC_k k c).denote ctx = _
      rw [mulConstC_k_eq_mulConstC, denote_mulConstC, mul_comm]; rfl
    | add k₂ m₂ q₂ =>
      show (Bool.rec (Bool.rec _ _ (Poly.add k₂ m₂ q₂).isMon_k) _ (Poly.add k₁ m₁ q₁).isMon_k : Poly).denote ctx = _
      cases h₁ : (Poly.add k₁ m₁ q₁).isMon_k
      · cases h₂ : (Poly.add k₂ m₂ q₂).isMon_k
        · show (sumB_k _ (mulTermsC_k _ _ c)).denote ctx = _
          rw [denote_sumB_k ctx _ (denote_combineC_k ctx), denoteList_mulTermsC_k]
        · show ((Poly.add k₂ m₂ q₂).mulByMonC_k _ c).denote ctx = _
          rw [denote_mulByMonC_k ctx _ h₂, mul_comm]
      · exact denote_mulByMonC_k ctx _ h₁

theorem Poly.denote_powBC_k (p : Poly) (k : Nat) : (powBC_k p k c).denote ctx = p.denote ctx ^ k := by
  induction k with
  | zero => show ((1 : Int) : α) = _; rw [intCast_one, pow_zero]
  | succ k ih =>
    cases k with
    | zero => show p.denote ctx = _; rw [pow_succ, pow_zero, one_mul]
    | succ k =>
      show (p.mulBC_k (powBC_k p (k + 1) c) c).denote ctx = _
      rw [denote_mulBC_k, ih, pow_succ (n := k + 1), mul_comm]

theorem Expr.denote_powLeafBC_k (a : Expr) (k : Nat) (p : Poly) (h : p.denote ctx = a.denote ctx) :
    (a.powLeafBC_k k c p).denote ctx = a.denote ctx ^ k := by
  unfold powLeafBC_k
  cases hk : k.beq 0
  · have hk : k ≠ 0 := Nat.ne_of_beq_eq_false hk
    dsimp only
    cases a with
    | num n =>
      show ((Int.emod_k (Int.pow_k n k) (Int.ofNat c) : Int) : α) = _
      rw [Int.emod_k_eq, Int.pow_k_eq, Int.ofNat_eq_natCast, IsCharP.intCast_emod, intCast_pow]; simp [Expr.denote, denoteInt_eq]
    | var x => simp [Expr.denote, Poly.denote_ofMon, Mon.denote, Power.denote_eq, mul_one]
    | _ => rw [Poly.denote_powBC_k, h]
  · have hk : k = 0 := Nat.eq_of_beq_eq_true hk
    subst hk; show ((1 : Int) : α) = _; rw [intCast_one, pow_zero]

theorem Poly.denote_signBC_k (p : Poly) (s : Bool) : (p.signBC_k c s).denote ctx = bif s then -p.denote ctx else p.denote ctx := by
  cases s
  · rfl
  · show (p.mulConstC_k (Int.negSucc 0) c).denote ctx = _
    rw [mulConstC_k_eq_mulConstC, denote_mulConstC]; simp [intCast_neg, neg_mul, intCast_one, one_mul]

theorem Expr.denoteList_sumsBC_k (e : Expr) (s : Bool) (acc : List Poly) :
    Poly.denoteList ctx (e.sumsBC_k c s acc) = (bif s then -e.denote ctx else e.denote ctx) + Poly.denoteList ctx acc := by
  have hB (a : Expr) (ih : ∀ s acc, Poly.denoteList ctx (a.sumsBC_k c s acc) = (bif s then -a.denote ctx else a.denote ctx) + Poly.denoteList ctx acc) :
      (Poly.sumB_k (fun a b => a.combineC_k c b) (a.sumsBC_k c false [])).denote ctx = a.denote ctx := by
    rw [Poly.denote_sumB_k ctx _ (Poly.denote_combineC_k ctx), ih]; simp [Poly.denoteList, add_zero]
  induction e generalizing s acc with
  | num k =>
    show Poly.denote ctx (Poly.signBC_k (.num (Int.emod_k k (Int.ofNat c))) c s) + _ = _
    rw [Poly.denote_signBC_k]; simp [Expr.denote, Poly.denote, denoteInt_eq, Int.emod_k_eq, IsCharP.intCast_emod]
  | natCast k =>
    show Poly.denote ctx (Poly.signBC_k (.num (Int.emod_k (Int.ofNat k) (Int.ofNat c))) c s) + _ = _
    rw [Poly.denote_signBC_k]; simp [Expr.denote, Poly.denote, Int.emod_k_eq, IsCharP.intCast_emod, Ring.intCast_natCast]
  | intCast k =>
    show Poly.denote ctx (Poly.signBC_k (.num (Int.emod_k k (Int.ofNat c))) c s) + _ = _
    rw [Poly.denote_signBC_k]; simp [Expr.denote, Poly.denote, Int.emod_k_eq, IsCharP.intCast_emod]
  | var x => show Poly.denote ctx (Poly.signBC_k (Poly.ofVar x) c s) + _ = _; rw [Poly.denote_signBC_k, Poly.denote_ofVar]; rfl
  | neg a ih =>
    show Poly.denoteList ctx (a.sumsBC_k c (Bool.rec true false s) acc) = _
    rw [ih]; cases s <;> simp [Expr.denote, neg_neg]
  | add a b iha ihb =>
    show Poly.denoteList ctx (a.sumsBC_k c s (b.sumsBC_k c s acc)) = _
    rw [iha, ihb]; cases s <;> simp [Expr.denote, neg_add, add_assoc]
  | sub a b iha ihb =>
    show Poly.denoteList ctx (a.sumsBC_k c s (b.sumsBC_k c (Bool.rec true false s) acc)) = _
    rw [iha, ihb]; cases s <;> simp [Expr.denote, sub_eq_add_neg, neg_add, neg_neg, add_assoc]
  | mul a b iha ihb =>
    show (((Poly.sumB_k (fun a b => a.combineC_k c b) (a.sumsBC_k c false [])).mulBC_k
      (Poly.sumB_k (fun a b => a.combineC_k c b) (b.sumsBC_k c false [])) c).signBC_k c s).denote ctx + Poly.denoteList ctx acc = _
    rw [Poly.denote_signBC_k, Poly.denote_mulBC_k, hB a iha, hB b ihb]; rfl
  | pow a k ih =>
    show ((a.powLeafBC_k k c (Poly.sumB_k (fun a b => a.combineC_k c b) (a.sumsBC_k c false []))).signBC_k c s).denote ctx
      + Poly.denoteList ctx acc = _
    rw [Poly.denote_signBC_k, Expr.denote_powLeafBC_k ctx a k _ (hB a ih)]; rfl

theorem Expr.denote_toPolyXC_k (bal : Bool) (e : Expr) : (e.toPolyXC_k bal c).denote ctx = e.denote ctx := by
  cases bal
  · show (e.toPolyC_k c).denote ctx = _; rw [toPolyC_k_eq_toPolyC, denote_toPolyC]
  · show (Poly.sumB_k (fun a b => a.combineC_k c b) (e.sumsBC_k c false [])).denote ctx = _
    rw [Poly.denote_sumB_k ctx _ (Poly.denote_combineC_k ctx), denoteList_sumsBC_k]
    simp [Poly.denoteList, add_zero]

end

theorem Expr.eq_of_toPolyC_eq_toExpr {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (bal : Bool) (a b : Expr) (p : Poly)
    (h₁ : p = a.toPolyXC_k bal c) (h₂ : b = p.toExpr_k) : a.denote ctx = b.denote ctx := by
  subst h₁ h₂; rw [Poly.toExpr_k_eq, Poly.denote_toExpr, Expr.denote_toPolyXC_k]


/-!
Hint-directed addition of polynomials. Certificates state the result `p` of a step and prove
`p = a.mergeHint hs b` by `Eq.refl`, so the kernel checks the step by definitional equality: the
monomials that `p` shares with `a` are compared by pointer after the kernel's hash-consing, and the
hints `hs` place the monomials of `b` without comparing monomial orders.
-/

/--
`mergeHead norm c k m a cont` places the monomial `k*m` at the head of `a`, then continues with
`cont` on the remaining part of `a`. If `c` is `true` and the head of `a` is `k₁*m`, the two are
added (with coefficient `norm (k₁ + k)`, dropped if zero), otherwise `k*m` is inserted.
-/
noncomputable def Poly.mergeHead (norm : Int → Int) (c : Bool) (k : Int) (m : Mon) (a : Poly) (cont : Poly → Poly) : Poly :=
  Bool.rec (.add k m (cont a))
    (Poly.rec (fun _ => .add k m (cont a))
      (fun k₁ m₁ a' _ => Bool.rec (.add k m (cont a))
        (Bool.rec (.add (norm (Int.add_k k₁ k)) m₁ (cont a')) (cont a') (Int.beqZero_k (norm (Int.add_k k₁ k))))
        (Mon.beq' m₁ m)) a)
    c

/-- `skipThen n a f` keeps the first `n` monomials of `a` and applies `f` to the rest. -/
noncomputable def Poly.skipThen (n : Nat) (a : Poly) (f : Poly → Poly) : Poly :=
  Nat.rec (motive := fun _ => Poly → Poly) f
    (fun _ ih a => Poly.rec (fun k => ih (.num k)) (fun k m a' _ => .add k m (ih a')) a) n a

/--
`mergeHintG norm addK comb hs a b` adds `a` and `b` following the hints `hs`, one per monomial of
`b`, in order. `mergeHint` and `mergeHintC` instantiate `norm`, `addK` and `comb` for rings
without and with a characteristic. A hint `h = 2*n + c` places the head monomial `k*m` of `b`:
- the first `n = h / 2` monomials of the remaining part of `a` are kept, since they are greater
  than `m`;
- if `c = h % 2` is `1`, the next monomial of `a` is `k₁*m`, and the two are added into
  `norm (k₁ + k) * m`, which is dropped if its coefficient is zero;
- if `c` is `0`, `k*m` is inserted before the next monomial of `a`.

The next hint continues after `m` in both `a` and `b`. When `b` reaches its constant, it is added
with `addK`. If the hints run out before the monomials of `b`, the rest is added with `comb`.
Wrong hints produce a wrong sum, and the certificate `p = a.mergeHint hs b` then fails to check.

Example: in the order `x³ > x² > x`, with `a = 5*x³ + 2*x² + 7` and `b = 3*x² + 4*x + 1`,
`hs = [3, 0]`:
- `3 = 2*1 + 1` keeps `5*x³` and adds `3*x²` to `2*x²`, giving `5*x²`;
- `0 = 2*0 + 0` inserts `4*x` before the constant `7`;
- the constant `1` of `b` is added to `7`.

The sum is `5*x³ + 5*x² + 4*x + 8`. With `a = x² + 2*x` and `b = -x² + 1`, `hs = [1]` adds `-x²`
to `x²`, drops the zero monomial, and the sum is `2*x + 1`.
-/
noncomputable def Poly.mergeHintG (norm : Int → Int) (addK : Poly → Int → Poly) (comb : Poly → Poly → Poly)
    (hs : List Nat) : Poly → Poly → Poly :=
  List.rec (motive := fun _ => Poly → Poly → Poly)
    (fun a b => Poly.rec (fun k => addK a k) (fun _ _ _ _ => comb a b) b)
    (fun h _ ih a b => Poly.skipThen (Nat.div h 2) a (fun a =>
      Poly.rec (fun k => addK a k) (fun k m b' _ => Poly.mergeHead norm (Nat.beq (Nat.mod h 2) 1) k m a (fun a => ih a b')) b))
    hs

theorem Poly.denote_skipThen {α} [Ring α] (ctx : Context α) (f : Poly → Poly) (X : α)
    (hf : ∀ a, (f a).denote ctx = a.denote ctx + X) (n : Nat) (a : Poly) :
    (Poly.skipThen n a f).denote ctx = a.denote ctx + X := by
  induction n generalizing a with
  | zero => exact hf a
  | succ n ih =>
    cases a with
    | num k => exact ih (.num k)
    | add k m a' =>
      show (Poly.add k m (Poly.skipThen n a' f)).denote ctx = _
      simp only [denote, ih, Semiring.add_assoc]

theorem Poly.denote_mergeHead {α} [Ring α] (ctx : Context α) (norm : Int → Int)
    (hn : ∀ k, ((norm k : Int) : α) = (k : α)) (cont : Poly → Poly) (Y : α)
    (hcont : ∀ a, (cont a).denote ctx = a.denote ctx + Y) (c : Bool) (k : Int) (m : Mon) (a : Poly) :
    (Poly.mergeHead norm c k m a cont).denote ctx = a.denote ctx + (k • m.denote ctx + Y) := by
  have hins : (Poly.add k m (cont a)).denote ctx = a.denote ctx + (k • m.denote ctx + Y) := by
    simp only [denote, hcont]; rw [add_left_comm]
  cases c
  · exact hins
  · cases a with
    | num k₁ => exact hins
    | add k₁ m₁ a' =>
      show (Bool.rec (.add k m (cont (.add k₁ m₁ a')))
        (Bool.rec (.add (norm (Int.add_k k₁ k)) m₁ (cont a')) (cont a') (Int.beqZero_k (norm (Int.add_k k₁ k))))
        (Mon.beq' m₁ m) : Poly).denote ctx = _
      cases hm : Mon.beq' m₁ m
      · exact hins
      · rw [Mon.beq'_eq] at hm; subst hm
        have hsum : (norm (Int.add_k k₁ k)) • m₁.denote ctx = k₁ • m₁.denote ctx + k • m₁.denote ctx := by
          rw [zsmul_eq_intCast_mul, zsmul_eq_intCast_mul, zsmul_eq_intCast_mul, hn, Int.add_k_eq, Int.add_def, Ring.intCast_add, right_distrib]
        cases hz : Int.beqZero_k (norm (Int.add_k k₁ k))
        · show (Poly.add (norm (Int.add_k k₁ k)) m₁ (cont a')).denote ctx = _
          simp only [denote, hcont, hsum, Semiring.add_assoc, add_left_comm]
        · rw [Int.beqZero_k_eq, beq_iff_eq] at hz
          rw [hz, zsmul_eq_intCast_mul, Ring.intCast_zero, Semiring.zero_mul] at hsum
          show (cont a').denote ctx = _
          simp only [denote, hcont]
          have : k₁ • m₁.denote ctx + denote ctx a' + (k • m₁.denote ctx + Y) =
              denote ctx a' + Y + (k₁ • m₁.denote ctx + k • m₁.denote ctx) := by
            simp only [Semiring.add_assoc, add_comm, add_left_comm]
          rw [this, ← hsum, add_zero]

theorem Poly.denote_mergeHintG {α} [Ring α] (ctx : Context α) (norm : Int → Int) (addK : Poly → Int → Poly)
    (comb : Poly → Poly → Poly) (hn : ∀ k, ((norm k : Int) : α) = (k : α))
    (ha : ∀ a k, (addK a k).denote ctx = a.denote ctx + (k : α))
    (hc : ∀ a b, (comb a b).denote ctx = a.denote ctx + b.denote ctx)
    (hs : List Nat) (a b : Poly) :
    (Poly.mergeHintG norm addK comb hs a b).denote ctx = a.denote ctx + b.denote ctx := by
  induction hs generalizing a b with
  | nil =>
    cases b with
    | num k => exact ha a k
    | add k m b' => exact hc a _
  | cons h hs ih =>
    cases b with
    | num k =>
      exact Poly.denote_skipThen ctx _ _ (fun a => ha a k) _ a
    | add k m b' =>
      exact Poly.denote_skipThen ctx _ _
        (fun a => Poly.denote_mergeHead ctx norm hn (fun a => mergeHintG norm addK comb hs a b') _ (fun a => ih a b') _ k m a) _ a

noncomputable def Poly.mergeHint (hs : List Nat) (a b : Poly) : Poly :=
  Poly.mergeHintG (fun k => k) Poly.addConst_k Poly.combine_k hs a b

noncomputable def Poly.mergeHintC (c : Nat) (hs : List Nat) (a b : Poly) : Poly :=
  Poly.mergeHintG (fun k => Int.emod_k k (Int.ofNat c)) (fun a k => a.addConstC_k k c) (fun a b => a.combineC_k c b) hs a b

theorem Poly.denote_mergeHint {α} [Ring α] (ctx : Context α) (hs : List Nat) (a b : Poly) :
    (a.mergeHint hs b).denote ctx = a.denote ctx + b.denote ctx :=
  Poly.denote_mergeHintG ctx _ _ _ (fun _ => rfl)
    (fun a k => by rw [addConst_k_eq_addConst, denote_addConst])
    (fun a b => by rw [combine_k_eq_combine, denote_combine]) hs a b

theorem Poly.denote_mergeHintC {α c} [Ring α] [IsCharP α c] (ctx : Context α) (hs : List Nat) (a b : Poly) :
    (a.mergeHintC c hs b).denote ctx = a.denote ctx + b.denote ctx :=
  Poly.denote_mergeHintG ctx _ _ _ (fun k => by rw [Int.emod_k_eq, Int.ofNat_eq_natCast, IsCharP.intCast_emod])
    (fun a k => by rw [addConstC_k_eq_addConstC, denote_addConstC])
    (fun a b => by rw [combineC_k_eq_combineC, denote_combineC]) hs a b

/--
A sum of multiples `k * m * p` of polynomials `p`, combined with hinted merges (`Poly.mergeHint`).
It certifies a chain of simplification steps at once: the kernel adds the multiples in a balanced
tree and then adds their sum to the initial polynomial once.

Example: a chain of four steps simplifies `p₁` by the basis polynomials `q₁`, ..., `q₄`:
```
p₂ = p₁ + k₁*m₁*q₁,  p₃ = p₂ + k₂*m₂*q₂,  p₄ = p₃ + k₃*m₃*q₃,  p = p₄ + k₄*m₄*q₄
```
Checking each step copies most of the large `pᵢ`. Instead, `Stepwise.simps ctx p₁ p t hs` proves
`p.denote ctx = 0` from `p₁.denote ctx = 0` and `t.AllZero ctx`, where
```
t = .node hs₀ (.node hs₁ (.leaf k₁ m₁ q₁) (.leaf k₂ m₂ q₂))
              (.node hs₂ (.leaf k₃ m₃ q₃) (.leaf k₄ m₄ q₄))
```
The certificate `p = p₁.mergeHint hs t.eval` adds the small multiples first, and `hs` merges their
sum into `p₁` once. The intermediate `p₂`, `p₃` and `p₄` are never stated.
-/
inductive SumTree where
  | leaf (k : Int) (m : Mon) (p : Poly)
  | node (hs : List Nat) (a b : SumTree)

noncomputable def SumTree.eval (t : SumTree) : Poly :=
  SumTree.rec (motive := fun _ => Poly) (fun k m p => p.mulMon_k k m) (fun hs _ _ a b => a.mergeHint hs b) t

noncomputable def SumTree.evalC (c : Nat) (t : SumTree) : Poly :=
  SumTree.rec (motive := fun _ => Poly) (fun k m p => p.mulMonC_k k m c) (fun hs _ _ a b => a.mergeHintC c hs b) t

/-- Every polynomial of the leaves of `t` denotes `0`. -/
noncomputable def SumTree.AllZero {α} [Ring α] (ctx : Context α) (t : SumTree) : Prop :=
  SumTree.rec (motive := fun _ => Prop) (fun _ _ p => p.denote ctx = 0) (fun _ _ _ a b => a ∧ b) t

theorem SumTree.denote_eval {α} [CommRing α] (ctx : Context α) (t : SumTree) (h : t.AllZero ctx) :
    t.eval.denote ctx = 0 := by
  induction t with
  | leaf k m p =>
    replace h : p.denote ctx = 0 := h
    show (p.mulMon_k k m).denote ctx = 0
    simp [Poly.denote_mulMon, h, mul_zero]
  | node hs a b iha ihb =>
    obtain ⟨ha, hb⟩ := h
    show (a.eval.mergeHint hs b.eval).denote ctx = 0
    rw [Poly.denote_mergeHint, iha ha, ihb hb, add_zero]

theorem SumTree.denote_evalC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (t : SumTree) (h : t.AllZero ctx) :
    (t.evalC c).denote ctx = 0 := by
  induction t with
  | leaf k m p =>
    replace h : p.denote ctx = 0 := h
    show (p.mulMonC_k k m c).denote ctx = 0
    simp [Poly.denote_mulMonC, h, mul_zero]
  | node hs a b iha ihb =>
    obtain ⟨ha, hb⟩ := h
    show ((a.evalC c).mergeHintC c hs (b.evalC c)).denote ctx = 0
    rw [Poly.denote_mergeHintC, iha ha, ihb hb, add_zero]

namespace Stepwise
/-!
Theorems for stepwise proof-term construction
-/
noncomputable def core_cert (lhs rhs : Expr) (p : Poly) : Bool :=
  (lhs.sub rhs).toPoly_k.beq' p

theorem core {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : p = (lhs.sub rhs).toPoly_k → lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  intro; subst p; simp only [Expr.toPoly_k_eq_toPoly]
  simp [Expr.denote_toPoly, Expr.denote]
  simp [sub_eq_zero_iff]

theorem superpose {α} [CommRing α] (ctx : Context α) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = (p₁.mulMon_k k₁ m₁).mergeHint hs (p₂.mulMon_k k₂ m₂) → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHint]
  simp [Poly.denote_mulMon, h₁, h₂, mul_zero, add_zero]

theorem simps {α} [CommRing α] (ctx : Context α) (p₁ : Poly) (p : Poly) (t : SumTree) (hs : List Nat)
    : p = p₁.mergeHint hs t.eval → t.AllZero ctx → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro h ht h₁
  rw [h, Poly.denote_mergeHint, SumTree.denote_eval ctx t ht, h₁, add_zero]

theorem simp1 {α} [CommRing α] (ctx : Context α) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = p₁.mergeHint hs (p₂.mulMon_k k₂ m₂) → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHint]
  simp [Poly.denote_mulMon, h₁, h₂, mul_zero, add_zero]

theorem simp {α} [CommRing α] (ctx : Context α) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = (p₁.mulConst_k k₁).mergeHint hs (p₂.mulMon_k k₂ m₂) → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHint]
  simp [Poly.denote_mulMon, Poly.denote_mulConst, h₁, h₂, mul_zero, add_zero]

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
  !Int.beq' k 0 |>.and (p.mulConst_k k |>.beq' p₁)

theorem div {α} [CommRing α] (ctx : Context α) [NoNatZeroDivisors α] (p₁ : Poly) (k : Int) (p : Poly)
    : div_cert p₁ k p → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [div_cert]; intro hnz _ h; subst p₁
  simp [Poly.denote_mulConst, ← zsmul_eq_intCast_mul] at h
  exact no_int_zero_divisors hnz h

noncomputable def unsat_eq_cert (p : Poly) (k : Int) : Bool :=
  !Int.beq' k 0 |>.and (p.beq' (.num k))

theorem unsat_eq {α} [CommRing α] (ctx : Context α) [IsCharP α 0] (p : Poly) (k : Int)
    : unsat_eq_cert p k → p.denote ctx = 0 → False := by
  simp [unsat_eq_cert]; intro h _; subst p; simp [Poly.denote]
  have := IsCharP.intCast_eq_zero_iff (α := α) 0 k
  simp [h] at this
  assumption

theorem d_init {α} [CommRing α] (ctx : Context α) (p : Poly) : (1:Int) * p.denote ctx = p.denote ctx := by
  rw [intCast_one, one_mul]

theorem d_step1 {α} [CommRing α] (ctx : Context α) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = p₁.mergeHint hs (p₂.mulMon_k k₂ m₂) → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHint]
  simp [Poly.denote_mulMon, h₂, mul_zero, add_zero, h₁]

theorem d_steps {α} [CommRing α] (ctx : Context α) (k : Int) (init : Poly) (p₁ : Poly) (p : Poly) (t : SumTree) (hs : List Nat)
    : p = p₁.mergeHint hs t.eval → t.AllZero ctx → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro h ht h₁
  rw [h, Poly.denote_mergeHint, SumTree.denote_eval ctx t ht, add_zero, h₁]

theorem d_stepk {α} [CommRing α] (ctx : Context α) (k₁ : Int) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = (p₁.mulConst_k k₁).mergeHint hs (p₂.mulMon_k k₂ m₂) → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → (k₁*k : Int) * init.denote ctx = p.denote ctx := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHint]
  simp [Poly.denote_mulMon, Poly.denote_mulConst, h₂, mul_zero, add_zero]
  rw [intCast_mul, mul_assoc, h₁]

noncomputable def imp_1eq_cert (lhs rhs : Expr) (p₁ p₂ : Poly) : Bool :=
  (lhs.sub rhs).toPoly_k.beq' p₁ |>.and (p₂.beq' (.num 0))

theorem imp_1eq {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_1eq_cert lhs rhs p₁ p₂ → (1:Int) * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_1eq_cert, intCast_one, one_mul]; intro _ _; subst p₁ p₂
  simp [Expr.denote_toPoly, Expr.denote, sub_eq_zero_iff, Poly.denote, intCast_zero]

noncomputable def imp_keq_cert (lhs rhs : Expr) (k : Int) (p₁ p₂ : Poly) : Bool :=
  !Int.beq' k 0 |>.and ((lhs.sub rhs).toPoly_k.beq' p₁ |>.and (p₂.beq' (.num 0)))

theorem imp_keq  {α} [CommRing α] (ctx : Context α) [NoNatZeroDivisors α] (k : Int) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_keq_cert lhs rhs k p₁ p₂ → k * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_keq_cert]; intro hnz _ _; subst p₁ p₂
  simp [Expr.denote_toPoly, Expr.denote, Poly.denote, intCast_zero, ← zsmul_eq_intCast_mul]
  intro h; replace h := no_int_zero_divisors hnz h
  rw [← sub_eq_zero_iff, h]

theorem coreC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : p = (lhs.sub rhs).toPolyC_k c → lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  intro; subst p; simp only [Expr.toPolyC_k_eq_toPolyC]
  simp [Expr.denote_toPolyC, Expr.denote]
  simp [sub_eq_zero_iff]

theorem superposeC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (m₁ : Mon) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = (p₁.mulMonC_k k₁ m₁ c).mergeHintC c hs (p₂.mulMonC_k k₂ m₂ c) → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHintC]
  simp [Poly.denote_mulMonC, h₁, h₂, mul_zero, add_zero]

noncomputable def mul_certC (p₁ : Poly) (k : Int) (p : Poly) (c : Nat) : Bool :=
  p₁.mulConstC_k k c |>.beq' p

theorem mulC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ : Poly) (k : Int) (p : Poly)
    : mul_certC p₁ k p c → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [mul_certC]; intro _ h; subst p
  simp [Poly.denote_mulConstC, *, mul_zero]

noncomputable def div_certC (p₁ : Poly) (k : Int) (p : Poly) (c : Nat) : Bool :=
  !Int.beq' k 0 |>.and ((p.mulConstC_k k c).beq' p₁)

theorem divC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) [NoNatZeroDivisors α] (p₁ : Poly) (k : Int) (p : Poly)
    : div_certC p₁ k p c → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  simp [div_certC]; intro hnz _ h; subst p₁
  simp [Poly.denote_mulConstC, ← zsmul_eq_intCast_mul] at h
  exact no_int_zero_divisors hnz h

theorem simpsC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ : Poly) (p : Poly) (t : SumTree) (hs : List Nat)
    : p = p₁.mergeHintC c hs (t.evalC c) → t.AllZero ctx → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro h ht h₁
  rw [h, Poly.denote_mergeHintC, SumTree.denote_evalC ctx t ht, h₁, add_zero]

theorem simp1C {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = p₁.mergeHintC c hs (p₂.mulMonC_k k₂ m₂ c) → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHintC]
  simp [Poly.denote_mulMonC, h₁, h₂, mul_zero, add_zero]

theorem simpC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = (p₁.mulConstC_k k₁ c).mergeHintC c hs (p₂.mulMonC_k k₂ m₂ c) → p₁.denote ctx = 0 → p₂.denote ctx = 0 → p.denote ctx = 0 := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHintC]
  simp [Poly.denote_mulMonC, Poly.denote_mulConstC, h₁, h₂, mul_zero, add_zero]

noncomputable def unsat_eq_certC (p : Poly) (k : Int) (c : Nat) : Bool :=
  !Int.beq' (Int.emod_k k (Int.ofNat c)) 0 |>.and (p.beq' (.num k))

theorem unsat_eqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (p : Poly) (k : Int)
    : unsat_eq_certC p k c → p.denote ctx = 0 → False := by
  simp [unsat_eq_certC]; intro h _; subst p; simp [Poly.denote]
  have := IsCharP.intCast_eq_zero_iff (α := α) c k
  simp [h] at this
  assumption

theorem d_step1C {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = p₁.mergeHintC c hs (p₂.mulMonC_k k₂ m₂ c) → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHintC]
  simp [Poly.denote_mulMonC, h₂, mul_zero, add_zero, h₁]

theorem d_stepsC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (init : Poly) (p₁ : Poly) (p : Poly) (t : SumTree) (hs : List Nat)
    : p = p₁.mergeHintC c hs (t.evalC c) → t.AllZero ctx → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro h ht h₁
  rw [h, Poly.denote_mergeHintC, SumTree.denote_evalC ctx t ht, add_zero, h₁]

theorem d_stepkC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k₁ : Int) (k : Int) (init : Poly) (p₁ : Poly) (k₂ : Int) (m₂ : Mon) (p₂ : Poly) (p : Poly) (hs : List Nat)
    : p = (p₁.mulConstC_k k₁ c).mergeHintC c hs (p₂.mulMonC_k k₂ m₂ c) → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → (k₁*k : Int) * init.denote ctx = p.denote ctx := by
  intro h h₁ h₂
  rw [h, Poly.denote_mergeHintC]
  simp [Poly.denote_mulMonC, Poly.denote_mulConstC, h₂, mul_zero, add_zero]
  rw [intCast_mul, mul_assoc, h₁]

noncomputable def imp_1eq_certC (lhs rhs : Expr) (p₁ p₂ : Poly) (c : Nat) : Bool :=
  ((lhs.sub rhs).toPolyC_k c).beq' p₁ |>.and (p₂.beq' (.num 0))

theorem imp_1eqC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (p₁ p₂ : Poly)
    : imp_1eq_certC lhs rhs p₁ p₂ c → (1:Int) * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  simp [imp_1eq_certC, intCast_one, one_mul]; intro _ _; subst p₁ p₂
  simp [Expr.denote_toPolyC, Expr.denote, sub_eq_zero_iff, Poly.denote, intCast_zero]

noncomputable def imp_keq_certC (lhs rhs : Expr) (k : Int) (p₁ p₂ : Poly) (c : Nat) : Bool :=
  !Int.beq' k 0 |>.and (((lhs.sub rhs).toPolyC_k c).beq' p₁ |>.and (p₂.beq' (.num 0)))

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
  simp only [core_cert, Poly.beq'_eq]; intro h; exact core ctx lhs rhs p h.symm

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
  replace h₁ := congrArg (Int.cast (R := α) a * ·) h₁; try simp at h₁ -- TODO(kmill): remove simp after stage0 update
  rw [← Ring.intCast_mul, Ring.intCast_zero, Semiring.mul_zero] at h₁
  replace h₂ := congrArg (Int.cast (R := α) b * ·) h₂; try simp at h₂ -- TODO(kmill): remove simp after stage0 update
  rw [← Ring.intCast_mul, Ring.intCast_zero, Semiring.mul_zero] at h₂
  replace h₁ := congrArg (· + Int.cast (b * m)) h₁; try simp at h₁ -- TODO(kmill): remove simp after stage0 update
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
  p₂.beq' (.num c) |>.and (p.beq' (p₁.normEq0 c))

theorem d_normEq0 {α} [CommRing α] (ctx : Context α) (k : Int) (c : Nat) (init : Poly) (p₁ p₂ p : Poly)
    : d_normEq0_cert c p₁ p₂ p → k * init.denote ctx = p₁.denote ctx → p₂.denote ctx = 0 → k * init.denote ctx = p.denote ctx := by
  simp [d_normEq0_cert]; intro _ h₁ h₂; subst p p₂; simp [Poly.denote]
  intro h; rw [p₁.normEq0_eq] <;> assumption

noncomputable def norm_int_cert (e : Expr) (p : Poly) : Bool :=
  e.toPoly_k.beq' p

theorem norm_int (ctx : Context Int) (e : Expr) (p : Poly) : norm_int_cert e p → e.denote ctx = p.denote' ctx := by
  simp [norm_int_cert, Poly.denote'_eq_denote]; intro; subst p; simp [Expr.denote_toPoly]

/-!
Kernel-reduction variants of `Poly.denote'`: `cutsat` states the result of `norm_int` with
`Poly.denote'_k`, which the kernel unfolds to match it with its own polynomials.
-/

noncomputable def Mon.denote'_k.go {α} [Semiring α] (ctx : Context α) (m : Mon) : α → α :=
  Mon.rec (fun acc => acc) (fun pw _ ih acc => ih (acc * pw.denote ctx)) m

noncomputable def Mon.denote'_k {α} [Semiring α] (ctx : Context α) (m : Mon) : α :=
  Mon.rec 1 (fun pw m _ => Mon.denote'_k.go ctx m (pw.denote ctx)) m

theorem Mon.denote'_k_eq {α} [Semiring α] (ctx : Context α) (m : Mon) : m.denote'_k ctx = m.denote' ctx := by
  have hgo : ∀ m acc, Mon.denote'_k.go ctx m acc = Mon.denote'.go ctx m acc := by
    intro m; induction m with
    | unit => intro acc; rfl
    | mult pw m ih => intro acc; exact ih _
  cases m with
  | unit => rfl
  | mult pw m => exact hgo m _

noncomputable def denoteTerm_k {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) : α :=
  Bool.rec (k • Mon.denote'_k ctx m) (Mon.denote'_k ctx m) (Int.beq' k 1)

theorem denoteTerm_k_eq {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) : denoteTerm_k ctx k m = denoteTerm ctx k m := by
  unfold denoteTerm_k denoteTerm
  rw [Mon.denote'_k_eq, show Int.beq' k 1 = (k == 1) from by simp [Int.beq'_eq_beq]]
  cases k == 1 <;> rfl

noncomputable def Poly.denote'_k.go {α} [Ring α] (ctx : Context α) (p : Poly) : α → α :=
  Poly.rec (fun k acc => Bool.rec (acc + Int.cast k) acc (Int.beqZero_k k))
    (fun k m _ ih acc => ih (acc + denoteTerm_k ctx k m)) p

noncomputable def Poly.denote'_k {α} [Ring α] (ctx : Context α) (p : Poly) : α :=
  Poly.rec (fun k => Int.cast k) (fun k m p _ => Poly.denote'_k.go ctx p (denoteTerm_k ctx k m)) p

theorem Poly.denote'_k_eq {α} [Ring α] (ctx : Context α) (p : Poly) : p.denote'_k ctx = p.denote' ctx := by
  have hgo : ∀ p acc, Poly.denote'_k.go ctx p acc = Poly.denote'.go ctx p acc := by
    intro p; induction p with
    | num k =>
      intro acc
      show Bool.rec (motive := fun _ => α) _ _ (Int.beqZero_k k) = _
      rw [Int.beqZero_k_eq]
      cases hk : k == 0
      · have h : k ≠ 0 := by simpa using hk
        show acc + Int.cast k = _; simp [Poly.denote'.go, h]
      · have h : k = 0 := by simpa using hk
        subst h; rfl
    | add k m p ih => intro acc; show Poly.denote'_k.go ctx p _ = _; rw [ih, denoteTerm_k_eq]; rfl
  cases p with
  | num k => rfl
  | add k m p => show Poly.denote'_k.go ctx p _ = _; rw [hgo, denoteTerm_k_eq]; rfl

theorem norm_int_k (ctx : Context Int) (e : Expr) (p : Poly) : norm_int_cert e p → e.denote ctx = p.denote'_k ctx := by
  rw [Poly.denote'_k_eq]; exact norm_int ctx e p

/-!
Helper theorems for normalizing ring constraints in the `grind order` module.
-/

/-!
Relation certificates over the polynomials of the normalized sides: `p` is the polynomial of
`a - b`, and `a'`, `b'` are the `Expr` spellings of `pa`, `pb` with `p = pa - pb`. Every
hypothesis is checked by definitional equality.
-/

theorem sub_eq_of_toExpr {α} [CommRing α] (ctx : Context α) (bal : Bool) (a b a' b' : Expr) (p pa pb : Poly)
    (h₁ : p = (a.sub b).toPolyX_k bal) (h₂ : a' = pa.toExpr_k) (h₃ : b' = pb.toExpr_k)
    (h₄ : p = pa.combine_k (pb.mulConst_k (Int.negSucc 0))) :
    a.denote ctx - b.denote ctx = a'.denote ctx - b'.denote ctx := by
  have e₁ := congrArg (Poly.denote ctx) h₁
  have e₄ := congrArg (Poly.denote ctx) h₄
  rw [Expr.denote_toPolyX_k] at e₁
  rw [Poly.combine_k_eq_combine, Poly.mulConst_k_eq_mulConst, Poly.denote_combine, Poly.denote_mulConst] at e₄
  subst h₂ h₃
  rw [Poly.toExpr_k_eq, Poly.toExpr_k_eq, Poly.denote_toExpr, Poly.denote_toExpr]
  replace e₁ : p.denote ctx = a.denote ctx - b.denote ctx := e₁
  rw [← e₁, e₄, Int.negSucc_eq, Int.natCast_zero, Int.zero_add, Ring.intCast_neg, Ring.intCast_one,
    Ring.neg_mul, Semiring.one_mul, sub_eq_add_neg]

theorem sub_eq_of_toExprC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (bal : Bool) (a b a' b' : Expr) (p pa pb : Poly)
    (h₁ : p = (a.sub b).toPolyXC_k bal c) (h₂ : a' = pa.toExpr_k) (h₃ : b' = pb.toExpr_k)
    (h₄ : p = pa.combineC_k c (pb.mulConstC_k (Int.negSucc 0) c)) :
    a.denote ctx - b.denote ctx = a'.denote ctx - b'.denote ctx := by
  have e₁ := congrArg (Poly.denote ctx) h₁
  have e₄ := congrArg (Poly.denote ctx) h₄
  rw [Expr.denote_toPolyXC_k] at e₁
  rw [Poly.combineC_k_eq_combineC, Poly.mulConstC_k_eq_mulConstC, Poly.denote_combineC, Poly.denote_mulConstC] at e₄
  subst h₂ h₃
  rw [Poly.toExpr_k_eq, Poly.toExpr_k_eq, Poly.denote_toExpr, Poly.denote_toExpr]
  replace e₁ : p.denote ctx = a.denote ctx - b.denote ctx := e₁
  rw [← e₁, e₄, Int.negSucc_eq, Int.natCast_zero, Int.zero_add, Ring.intCast_neg, Ring.intCast_one,
    Ring.neg_mul, Semiring.one_mul, sub_eq_add_neg]

theorem eq_norm_poly {α} [CommRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' rhs' : Expr) (p lp rp : Poly)
    (h₁ : p = (lhs.sub rhs).toPolyX_k bal) (h₂ : lhs' = lp.toExpr_k) (h₃ : rhs' = rp.toExpr_k)
    (h₄ : p = lp.combine_k (rp.mulConst_k (Int.negSucc 0))) :
    (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  rw [← AddCommGroup.sub_eq_zero_iff (a := lhs.denote ctx), sub_eq_of_toExpr ctx bal _ _ _ _ _ _ _ h₁ h₂ h₃ h₄, AddCommGroup.sub_eq_zero_iff]

theorem eq_norm_polyC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (bal : Bool) (lhs rhs lhs' rhs' : Expr) (p lp rp : Poly)
    (h₁ : p = (lhs.sub rhs).toPolyXC_k bal c) (h₂ : lhs' = lp.toExpr_k) (h₃ : rhs' = rp.toExpr_k)
    (h₄ : p = lp.combineC_k c (rp.mulConstC_k (Int.negSucc 0) c)) :
    (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  rw [← AddCommGroup.sub_eq_zero_iff (a := lhs.denote ctx), sub_eq_of_toExprC ctx bal _ _ _ _ _ _ _ h₁ h₂ h₃ h₄, AddCommGroup.sub_eq_zero_iff]

theorem le_norm_poly {α} [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' rhs' : Expr) (p lp rp : Poly)
    (h₁ : p = (rhs.sub lhs).toPolyX_k bal) (h₂ : lhs' = lp.toExpr_k) (h₃ : rhs' = rp.toExpr_k)
    (h₄ : p = rp.combine_k (lp.mulConst_k (Int.negSucc 0))) :
    (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  rw [← OrderedAdd.sub_nonneg_iff, sub_eq_of_toExpr ctx bal _ _ _ _ _ _ _ h₁ h₃ h₂ h₄, OrderedAdd.sub_nonneg_iff]

theorem le_norm_polyC {α c} [CommRing α] [IsCharP α c] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' rhs' : Expr) (p lp rp : Poly)
    (h₁ : p = (rhs.sub lhs).toPolyXC_k bal c) (h₂ : lhs' = lp.toExpr_k) (h₃ : rhs' = rp.toExpr_k)
    (h₄ : p = rp.combineC_k c (lp.mulConstC_k (Int.negSucc 0) c)) :
    (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  rw [← OrderedAdd.sub_nonneg_iff, sub_eq_of_toExprC ctx bal _ _ _ _ _ _ _ h₁ h₃ h₂ h₄, OrderedAdd.sub_nonneg_iff]

theorem lt_norm_poly {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' rhs' : Expr) (p lp rp : Poly)
    (h₁ : p = (rhs.sub lhs).toPolyX_k bal) (h₂ : lhs' = lp.toExpr_k) (h₃ : rhs' = rp.toExpr_k)
    (h₄ : p = rp.combine_k (lp.mulConst_k (Int.negSucc 0))) :
    (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  rw [← OrderedAdd.sub_pos_iff, sub_eq_of_toExpr ctx bal _ _ _ _ _ _ _ h₁ h₃ h₂ h₄, OrderedAdd.sub_pos_iff]

theorem lt_norm_polyC {α c} [CommRing α] [IsCharP α c] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' rhs' : Expr) (p lp rp : Poly)
    (h₁ : p = (rhs.sub lhs).toPolyXC_k bal c) (h₂ : lhs' = lp.toExpr_k) (h₃ : rhs' = rp.toExpr_k)
    (h₄ : p = rp.combineC_k c (lp.mulConstC_k (Int.negSucc 0) c)) :
    (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  rw [← OrderedAdd.sub_pos_iff, sub_eq_of_toExprC ctx bal _ _ _ _ _ _ _ h₁ h₃ h₂ h₄, OrderedAdd.sub_pos_iff]

/-!
Relations whose normal form is `p = 0`, `p ≤ 0` or `p < 0` (the `lhsOnly` mode of `Sym.Arith`): the
rendered side `lhs'` is checked against the polynomial `p` of `lhs - rhs` directly.
-/

theorem Poly.combine_k_num_zero (p : Poly) (k : Int) : p.combine_k ((Poly.num 0).mulConst_k k) = p := by
  have h : (Poly.num 0).mulConst k = .num 0 := by
    simp only [Poly.mulConst, Poly.mulConst.go, Int.mul_zero, cond_eq_ite]; split <;> (try split) <;> rfl
  rw [Poly.combine_k_eq_combine, Poly.mulConst_k_eq_mulConst, h]
  cases p <;> simp [Poly.combine, Poly.combine.go, Poly.addConst, cond]

theorem sub_eq_of_toExpr0 {α} [CommRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' : Expr) (p : Poly)
    (h₁ : p = (lhs.sub rhs).toPolyX_k bal) (h₂ : lhs' = p.toExpr_k) :
    lhs'.denote ctx = lhs.denote ctx - rhs.denote ctx := by
  subst h₁ h₂; rw [Poly.toExpr_k_eq, Poly.denote_toExpr, Expr.denote_toPolyX_k]; rfl

theorem eq_norm_poly0 {α} [CommRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' : Expr) (p : Poly)
    (h₁ : p = (lhs.sub rhs).toPolyX_k bal) (h₂ : lhs' = p.toExpr_k) :
    (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = (Expr.num 0).denote ctx) :=
  eq_norm_poly ctx bal lhs rhs lhs' (.num 0) p p (.num 0) h₁ h₂ rfl (Poly.combine_k_num_zero p _).symm

theorem le_norm_poly0 {α} [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' : Expr) (p : Poly)
    (h₁ : p = (lhs.sub rhs).toPolyX_k bal) (h₂ : lhs' = p.toExpr_k) :
    (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ (Expr.num 0).denote ctx) := by
  rw [sub_eq_of_toExpr0 ctx bal lhs rhs lhs' p h₁ h₂]
  show _ = (_ ≤ denoteInt 0)
  rw [denoteInt_eq, Ring.intCast_zero]
  apply propext
  rw [OrderedAdd.add_le_left_iff (c := - rhs.denote ctx), Ring.sub_eq_add_neg, AddCommGroup.add_neg_cancel]

theorem lt_norm_poly0 {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (bal : Bool) (lhs rhs lhs' : Expr) (p : Poly)
    (h₁ : p = (lhs.sub rhs).toPolyX_k bal) (h₂ : lhs' = p.toExpr_k) :
    (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < (Expr.num 0).denote ctx) := by
  rw [sub_eq_of_toExpr0 ctx bal lhs rhs lhs' p h₁ h₂]
  show _ = (_ < denoteInt 0)
  rw [denoteInt_eq, Ring.intCast_zero]
  apply propext
  rw [OrderedAdd.add_lt_left_iff (c := - rhs.denote ctx), Ring.sub_eq_add_neg, AddCommGroup.add_neg_cancel]

/-! Relations whose sides differ by a constant: the relation is `True` or `False`. -/

theorem sub_eq_of_toPolyX_k {α} [CommRing α] (ctx : Context α) (bal : Bool) (lhs rhs : Expr) (k : Int)
    (h : (lhs.sub rhs).toPolyX_k bal = .num k) : lhs.denote ctx - rhs.denote ctx = (k : α) := by
  have h' := congrArg (Poly.denote ctx) h
  rwa [Expr.denote_toPolyX_k] at h'

theorem eq_false_of_poly {α} [CommRing α] [IsCharP α 0] (ctx : Context α) (bal : Bool) (lhs rhs : Expr) (k : Int)
    (h : (lhs.sub rhs).toPolyX_k bal = .num k) (hk : Int.beqZero_k k = false) : (lhs.denote ctx = rhs.denote ctx) = False := by
  have h' := sub_eq_of_toPolyX_k ctx bal lhs rhs k h
  rw [Int.beqZero_k_eq] at hk
  apply eq_false; intro he
  rw [he, AddCommGroup.sub_self] at h'
  have := (IsCharP.intCast_eq_zero_iff (α := α) 0 k).mp h'.symm
  simp at this; simp [this] at hk

theorem le_true_of_poly {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α)
    (bal : Bool) (lhs rhs : Expr) (n : Nat) (h : (rhs.sub lhs).toPolyX_k bal = .num (Int.ofNat n)) :
    (lhs.denote ctx ≤ rhs.denote ctx) = True := by
  have h' := sub_eq_of_toPolyX_k ctx bal rhs lhs _ h
  rw [Int.ofNat_eq_natCast, Ring.intCast_natCast] at h'
  apply eq_true
  rw [← OrderedAdd.sub_nonneg_iff, h']
  exact OrderedRing.natCast_nonneg

theorem lt_true_of_poly {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α)
    (bal : Bool) (lhs rhs : Expr) (n : Nat) (h : (rhs.sub lhs).toPolyX_k bal = .num (Int.ofNat (n + 1))) :
    (lhs.denote ctx < rhs.denote ctx) = True := by
  have h' := sub_eq_of_toPolyX_k ctx bal rhs lhs _ h
  rw [Int.ofNat_eq_natCast, Ring.intCast_natCast] at h'
  apply eq_true
  rw [← OrderedAdd.sub_pos_iff, h']
  exact OrderedRing.pos_natCast_of_pos _ (Nat.succ_pos n)

theorem le_false_of_poly {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α)
    (bal : Bool) (lhs rhs : Expr) (n : Nat) (h : (lhs.sub rhs).toPolyX_k bal = .num (Int.ofNat (n + 1))) :
    (lhs.denote ctx ≤ rhs.denote ctx) = False := by
  have h' := sub_eq_of_toPolyX_k ctx bal lhs rhs _ h
  rw [Int.ofNat_eq_natCast, Ring.intCast_natCast] at h'
  apply eq_false; intro hle
  have h₁ : 0 < lhs.denote ctx - rhs.denote ctx := by rw [h']; exact OrderedRing.pos_natCast_of_pos _ (Nat.succ_pos n)
  rw [OrderedAdd.sub_pos_iff] at h₁
  exact Std.lt_irrefl (Std.lt_of_le_of_lt hle h₁)

theorem lt_false_of_poly {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α)
    (bal : Bool) (lhs rhs : Expr) (n : Nat) (h : (lhs.sub rhs).toPolyX_k bal = .num (Int.ofNat n)) :
    (lhs.denote ctx < rhs.denote ctx) = False := by
  have h' := sub_eq_of_toPolyX_k ctx bal lhs rhs _ h
  rw [Int.ofNat_eq_natCast, Ring.intCast_natCast] at h'
  apply eq_false; intro hlt
  have h₁ : 0 ≤ lhs.denote ctx - rhs.denote ctx := by rw [h']; exact OrderedRing.natCast_nonneg
  rw [OrderedAdd.sub_nonneg_iff] at h₁
  exact Std.lt_irrefl (Std.lt_of_lt_of_le hlt h₁)

/-! Relations whose sides have the same polynomial `p`: each side is checked against `p` alone. -/

theorem eq_true_of_toPoly_eq {α} [CommRing α] (ctx : Context α) (bal₁ bal₂ : Bool) (lhs rhs : Expr) (p : Poly)
    (h₁ : p = lhs.toPolyX_k bal₁) (h₂ : p = rhs.toPolyX_k bal₂) : (lhs.denote ctx = rhs.denote ctx) = True := by
  have e₁ := Expr.denote_toPolyX_k ctx bal₁ lhs
  have e₂ := Expr.denote_toPolyX_k ctx bal₂ rhs
  rw [← h₁] at e₁; rw [← h₂] at e₂
  exact eq_true (e₁.symm.trans e₂)

theorem eq_true_of_toPolyC_eq {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (bal₁ bal₂ : Bool) (lhs rhs : Expr) (p : Poly)
    (h₁ : p = lhs.toPolyXC_k bal₁ c) (h₂ : p = rhs.toPolyXC_k bal₂ c) : (lhs.denote ctx = rhs.denote ctx) = True := by
  have e₁ := Expr.denote_toPolyXC_k ctx bal₁ lhs
  have e₂ := Expr.denote_toPolyXC_k ctx bal₂ rhs
  rw [← h₁] at e₁; rw [← h₂] at e₂
  exact eq_true (e₁.symm.trans e₂)

theorem le_true_of_toPoly_eq {α} [CommRing α] [LE α] [IsPreorder α] (ctx : Context α) (bal₁ bal₂ : Bool) (lhs rhs : Expr) (p : Poly)
    (h₁ : p = lhs.toPolyX_k bal₁) (h₂ : p = rhs.toPolyX_k bal₂) : (lhs.denote ctx ≤ rhs.denote ctx) = True := by
  rw [of_eq_true (eq_true_of_toPoly_eq ctx bal₁ bal₂ lhs rhs p h₁ h₂)]; exact eq_true (Std.le_refl _)

theorem lt_false_of_toPoly_eq {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] (ctx : Context α)
    (bal₁ bal₂ : Bool) (lhs rhs : Expr) (p : Poly)
    (h₁ : p = lhs.toPolyX_k bal₁) (h₂ : p = rhs.toPolyX_k bal₂) : (lhs.denote ctx < rhs.denote ctx) = False := by
  rw [of_eq_true (eq_true_of_toPoly_eq ctx bal₁ bal₂ lhs rhs p h₁ h₂)]; exact eq_false Std.lt_irrefl

/-!
Stepwise certificates for large products. The kernel evaluates the partial products of
`Poly.mulB_k` lazily, and evaluates each again at every level of the pairwise additions that
compares its monomials. These theorems state the polynomial of each large product, and the list of
its partial products, so that the kernel evaluates each partial product once, when it checks the
list by definitional equality, and adds the stated ones.
-/

theorem Expr.denote_eq_of_toPolyX {α} [CommRing α] (ctx : Context α) (bal : Bool) (e : Expr) (p : Poly)
    (h : p = e.toPolyX_k bal) : e.denote ctx = p.denote ctx := by
  rw [h, Expr.denote_toPolyX_k]

theorem Expr.denote_mul_of_terms {α} [CommRing α] (ctx : Context α) (a b : Expr) (pa pb : Poly) (ts : List Poly) (p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hb : b.denote ctx = pb.denote ctx)
    (ht : ts = pa.mulTerms_k pb) (hp : p = Poly.sumB_k Poly.combine_k ts) : (Expr.mul a b).denote ctx = p.denote ctx := by
  show a.denote ctx * b.denote ctx = _
  rw [ha, hb, hp, Poly.denote_sumB_k ctx _ (Poly.denote_combine_k ctx), ht, Poly.denoteList_mulTerms_k]

theorem Expr.denote_add_of {α} [CommRing α] (ctx : Context α) (a b : Expr) (pa pb p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hb : b.denote ctx = pb.denote ctx)
    (hp : p = pa.combine_k pb) : (Expr.add a b).denote ctx = p.denote ctx := by
  show a.denote ctx + b.denote ctx = _
  rw [ha, hb, hp, Poly.denote_combine_k]

theorem Expr.denote_sub_of {α} [CommRing α] (ctx : Context α) (a b : Expr) (pa pb p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hb : b.denote ctx = pb.denote ctx)
    (hp : p = pa.combine_k (pb.mulConst_k (Int.negSucc 0))) : (Expr.sub a b).denote ctx = p.denote ctx := by
  show a.denote ctx - b.denote ctx = _
  rw [ha, hb, hp, Poly.denote_combine_k, Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst]
  simp [sub_eq_add_neg, intCast_neg, neg_mul, intCast_one, one_mul]

/-- `a ^ (k + 1)` from `a ^ k`, multiplying by the polynomial `pa` of `a`. -/
theorem Expr.denote_pow_succ_of_terms {α} [CommRing α] (ctx : Context α) (a : Expr) (k : Nat) (pa q : Poly) (ts : List Poly) (p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hq : (Expr.pow a k).denote ctx = q.denote ctx)
    (ht : ts = pa.mulTerms_k q) (hp : p = Poly.sumB_k Poly.combine_k ts) : (Expr.pow a (k + 1)).denote ctx = p.denote ctx := by
  replace hq : a.denote ctx ^ k = q.denote ctx := hq
  show a.denote ctx ^ (k + 1) = _
  rw [hp, Poly.denote_sumB_k ctx _ (Poly.denote_combine_k ctx), ht, Poly.denoteList_mulTerms_k, ← hq, ← ha, pow_succ, mul_comm]

theorem Expr.denote_pow_one_of {α} [CommRing α] (ctx : Context α) (a : Expr) (pa : Poly)
    (ha : a.denote ctx = pa.denote ctx) : (Expr.pow a 1).denote ctx = pa.denote ctx := by
  show a.denote ctx ^ 1 = _
  rw [pow_succ, pow_zero, one_mul, ha]

theorem eq_true_of_denote_eq {α} [CommRing α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    (h₁ : lhs.denote ctx = p.denote ctx) (h₂ : rhs.denote ctx = p.denote ctx) : (lhs.denote ctx = rhs.denote ctx) = True :=
  eq_true (h₁.trans h₂.symm)

theorem Expr.denote_neg_of {α} [CommRing α] (ctx : Context α) (a : Expr) (pa p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hp : p = pa.mulConst_k (Int.negSucc 0)) : (Expr.neg a).denote ctx = p.denote ctx := by
  show - a.denote ctx = _
  rw [ha, hp, Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst]
  simp [intCast_neg, neg_mul, intCast_one, one_mul]

theorem le_true_of_denote_eq {α} [CommRing α] [LE α] [IsPreorder α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    (h₁ : lhs.denote ctx = p.denote ctx) (h₂ : rhs.denote ctx = p.denote ctx) : (lhs.denote ctx ≤ rhs.denote ctx) = True := by
  rw [h₁, h₂]; exact eq_true (Std.le_refl _)

theorem lt_false_of_denote_eq {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    (h₁ : lhs.denote ctx = p.denote ctx) (h₂ : rhs.denote ctx = p.denote ctx) : (lhs.denote ctx < rhs.denote ctx) = False := by
  rw [h₁, h₂]; exact eq_false Std.lt_irrefl

theorem Expr.eq_of_denote_eq_toExpr {α} [CommRing α] (ctx : Context α) (a b : Expr) (p : Poly)
    (h₁ : a.denote ctx = p.denote ctx) (h₂ : b = p.toExpr_k) : a.denote ctx = b.denote ctx := by
  subst h₂; rw [Poly.toExpr_k_eq, Poly.denote_toExpr, h₁]

/-! Stepwise certificates for large products in characteristic `c`, like `Expr.denote_mul_of_terms`. -/

section
variable {α c} [CommRing α] [IsCharP α c] (ctx : Context α)

theorem Expr.denote_eq_of_toPolyXC (bal : Bool) (e : Expr) (p : Poly)
    (h : p = e.toPolyXC_k bal c) : e.denote ctx = p.denote ctx := by
  rw [h, Expr.denote_toPolyXC_k]

theorem Expr.denote_mul_of_termsC (a b : Expr) (pa pb : Poly) (ts : List Poly) (p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hb : b.denote ctx = pb.denote ctx)
    (ht : ts = pa.mulTermsC_k pb c) (hp : p = Poly.sumB_k (fun a b => a.combineC_k c b) ts) :
    (Expr.mul a b).denote ctx = p.denote ctx := by
  show a.denote ctx * b.denote ctx = _
  rw [ha, hb, hp, Poly.denote_sumB_k ctx _ (Poly.denote_combineC_k ctx), ht, Poly.denoteList_mulTermsC_k]

theorem Expr.denote_add_ofC (a b : Expr) (pa pb p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hb : b.denote ctx = pb.denote ctx)
    (hp : p = pa.combineC_k c pb) : (Expr.add a b).denote ctx = p.denote ctx := by
  show a.denote ctx + b.denote ctx = _
  rw [ha, hb, hp, Poly.denote_combineC_k]

theorem Expr.denote_sub_ofC (a b : Expr) (pa pb p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hb : b.denote ctx = pb.denote ctx)
    (hp : p = pa.combineC_k c (pb.mulConstC_k (Int.negSucc 0) c)) : (Expr.sub a b).denote ctx = p.denote ctx := by
  show a.denote ctx - b.denote ctx = _
  rw [ha, hb, hp, Poly.denote_combineC_k, Poly.mulConstC_k_eq_mulConstC, Poly.denote_mulConstC]
  simp [sub_eq_add_neg, intCast_neg, neg_mul, intCast_one, one_mul]

theorem Expr.denote_neg_ofC (a : Expr) (pa p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hp : p = pa.mulConstC_k (Int.negSucc 0) c) : (Expr.neg a).denote ctx = p.denote ctx := by
  show - a.denote ctx = _
  rw [ha, hp, Poly.mulConstC_k_eq_mulConstC, Poly.denote_mulConstC]
  simp [intCast_neg, neg_mul, intCast_one, one_mul]

theorem Expr.denote_pow_succ_of_termsC (a : Expr) (k : Nat) (pa q : Poly) (ts : List Poly) (p : Poly)
    (ha : a.denote ctx = pa.denote ctx) (hq : (Expr.pow a k).denote ctx = q.denote ctx)
    (ht : ts = pa.mulTermsC_k q c) (hp : p = Poly.sumB_k (fun a b => a.combineC_k c b) ts) :
    (Expr.pow a (k + 1)).denote ctx = p.denote ctx := by
  replace hq : a.denote ctx ^ k = q.denote ctx := hq
  show a.denote ctx ^ (k + 1) = _
  rw [hp, Poly.denote_sumB_k ctx _ (Poly.denote_combineC_k ctx), ht, Poly.denoteList_mulTermsC_k, ← hq, ← ha, pow_succ, mul_comm]

end

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

/-! Variants of the theorems above for rings with a nonzero characteristic `c`. -/

noncomputable def norm_cnstrC_cert (lhs rhs lhs' rhs' : Expr) (c : Nat) : Bool :=
  ((rhs.sub lhs).toPolyC_k c).beq' ((rhs'.sub lhs').toPolyC_k c)

theorem le_norm_exprC {α c} [CommRing α] [IsCharP α c] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_cnstrC_cert lhs rhs lhs' rhs' c → (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  simp [norm_cnstrC_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPolyC] at h
  replace h : rhs.denote ctx - lhs.denote ctx = rhs'.denote ctx - lhs'.denote ctx := h
  rw [← OrderedAdd.sub_nonneg_iff, h, OrderedAdd.sub_nonneg_iff]

theorem lt_norm_exprC {α c} [CommRing α] [IsCharP α c] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_cnstrC_cert lhs rhs lhs' rhs' c → (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  simp [norm_cnstrC_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPolyC] at h
  replace h : rhs.denote ctx - lhs.denote ctx = rhs'.denote ctx - lhs'.denote ctx := h
  rw [← OrderedAdd.sub_pos_iff, h, OrderedAdd.sub_pos_iff]

noncomputable def norm_eqC_cert (lhs rhs lhs' rhs' : Expr) (c : Nat) : Bool :=
  ((lhs.sub rhs).toPolyC_k c).beq' ((lhs'.sub rhs').toPolyC_k c)

theorem eq_norm_exprC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_eqC_cert lhs rhs lhs' rhs' c → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  simp [norm_eqC_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPolyC] at h
  replace h : lhs.denote ctx - rhs.denote ctx = lhs'.denote ctx - rhs'.denote ctx := h
  rw [← AddCommGroup.sub_eq_zero_iff, h, AddCommGroup.sub_eq_zero_iff]

noncomputable def norm_eq_mulC_cert (lhs rhs lhs' rhs' : Expr) (k k' : Int) (c : Nat) : Bool :=
  (Int.beq' (Int.emod_k (Int.mul_k k k') (Int.ofNat c)) 1).and
    ((((lhs.sub rhs).toPolyC_k c).mulConstC_k k' c).beq' ((lhs'.sub rhs').toPolyC_k c))

/-- In characteristic `c`, an equation can be multiplied by `k'` when `k * k' ≡ 1` modulo `c`. -/
theorem eq_norm_mul_exprC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr) (k k' : Int)
    : norm_eq_mulC_cert lhs rhs lhs' rhs' k k' c → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  simp [norm_eq_mulC_cert]; intro hk h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPolyC, Poly.denote_mulConstC] at h
  replace h : (IntCast.intCast k' : α) * (lhs.denote ctx - rhs.denote ctx) = lhs'.denote ctx - rhs'.denote ctx := h
  have hkk : (IntCast.intCast k : α) * (IntCast.intCast k' : α) = 1 := by
    rw [← intCast_mul, ← IsCharP.intCast_emod c, hk, intCast_one]
  rw [← AddCommGroup.sub_eq_zero_iff, ← AddCommGroup.sub_eq_zero_iff (a := lhs'.denote ctx), ← h]
  constructor
  · intro h₁; rw [h₁, mul_zero]
  · intro h₁
    replace h₁ := congrArg ((IntCast.intCast k : α) * ·) h₁
    rw [← mul_assoc, hkk, one_mul, mul_zero] at h₁
    exact h₁

noncomputable def norm_cnstr_nc_cert (lhs rhs lhs' rhs' : Expr) : Bool :=
  (rhs.sub lhs).toPoly_nc_k.beq' (rhs'.sub lhs').toPoly_nc_k

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
  (lhs.sub rhs).toPoly_nc_k.beq' (lhs'.sub rhs').toPoly_nc_k

theorem eq_norm_expr_nc {α} [Ring α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_eq_nc_cert lhs rhs lhs' rhs' → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  simp [norm_eq_nc_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPoly_nc] at h
  replace h : lhs.denote ctx - rhs.denote ctx = lhs'.denote ctx - rhs'.denote ctx := h
  rw [← AddCommGroup.sub_eq_zero_iff, h, AddCommGroup.sub_eq_zero_iff]


noncomputable def norm_cnstrC_nc_cert (lhs rhs lhs' rhs' : Expr) (c : Nat) : Bool :=
  ((rhs.sub lhs).toPolyC_nc_k c).beq' ((rhs'.sub lhs').toPolyC_nc_k c)

theorem le_norm_exprC_nc {α c} [Ring α] [IsCharP α c] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_cnstrC_nc_cert lhs rhs lhs' rhs' c → (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  simp [norm_cnstrC_nc_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPolyC_nc] at h
  replace h : rhs.denote ctx - lhs.denote ctx = rhs'.denote ctx - lhs'.denote ctx := h
  rw [← OrderedAdd.sub_nonneg_iff, h, OrderedAdd.sub_nonneg_iff]

theorem lt_norm_exprC_nc {α c} [Ring α] [IsCharP α c] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_cnstrC_nc_cert lhs rhs lhs' rhs' c → (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  simp [norm_cnstrC_nc_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPolyC_nc] at h
  replace h : rhs.denote ctx - lhs.denote ctx = rhs'.denote ctx - lhs'.denote ctx := h
  rw [← OrderedAdd.sub_pos_iff, h, OrderedAdd.sub_pos_iff]

noncomputable def norm_eqC_nc_cert (lhs rhs lhs' rhs' : Expr) (c : Nat) : Bool :=
  ((lhs.sub rhs).toPolyC_nc_k c).beq' ((lhs'.sub rhs').toPolyC_nc_k c)

theorem eq_norm_exprC_nc {α c} [Ring α] [IsCharP α c] (ctx : Context α) (lhs rhs : Expr) (lhs' rhs' : Expr)
    : norm_eqC_nc_cert lhs rhs lhs' rhs' c → (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  simp [norm_eqC_nc_cert]; intro h
  replace h := congrArg (Poly.denote ctx) h; simp [Expr.denote_toPolyC_nc] at h
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
