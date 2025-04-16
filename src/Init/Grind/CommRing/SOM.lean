/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Lemmas
import Init.Data.Ord
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

-- TODO: add support for universes to Lean.RArray
inductive RArray (α : Type u) : Type u where
  | leaf : α → RArray α
  | branch : Nat → RArray α → RArray α → RArray α

def RArray.get (a : RArray α) (n : Nat) : α :=
  match a with
  | .leaf x => x
  | .branch p l r => if n < p then l.get n else r.get n

abbrev Context (α : Type u) := RArray α

def Var.denote (ctx : Context α) (v : Var) : α :=
  ctx.get v

def Expr.denote [CommRing α] (ctx : Context α) : Expr → α
  | .add a b  => denote ctx a + denote ctx b
  | .sub a b  => denote ctx a - denote ctx b
  | .mul a b  => denote ctx a * denote ctx b
  | .neg a    => -denote ctx a
  | .num k    => k
  | .var v    => v.denote ctx
  | .pow a k  => denote ctx a ^ k

structure Power where
  x : Var
  k : Nat
  deriving BEq, Repr

def Power.varLt (p₁ p₂ : Power) : Bool :=
  p₁.x.blt p₂.x

def Power.denote [CommRing α] (ctx : Context α) : Power → α
  | {x, k} =>
    match k with
    | 0 => 1
    | 1 => x.denote ctx
    | k => x.denote ctx ^ k

inductive Mon where
  | leaf (p : Power)
  | cons (p : Power) (m : Mon)
  deriving BEq, Repr

def Mon.denote [CommRing α] (ctx : Context α) : Mon → α
  | .leaf p => p.denote ctx
  | .cons p m => p.denote ctx * denote ctx m

def Mon.denote' [CommRing α] (ctx : Context α) : Mon → α
  | .leaf p => p.denote ctx
  | .cons p m => go (p.denote ctx) m
where
  go (acc : α) : Mon → α
    | .leaf p => acc * p.denote ctx
    | .cons p m => go (acc * p.denote ctx) m

def Mon.concat (m₁ m₂ : Mon) : Mon :=
  match m₁ with
  | .leaf p => .cons p m₂
  | .cons p m₁ => .cons p (concat m₁ m₂)

def Mon.mulPow (p : Power) (m : Mon) : Mon :=
  match m with
  | .leaf p' =>
    bif p.varLt p' then
      .cons p m
    else bif p'.varLt p then
      .cons p' (.leaf p)
    else
      .leaf { x := p.x, k := p.k + p'.k }
  | .cons p' m =>
    bif p.varLt p' then
      .cons p (.cons p' m)
    else bif p'.varLt p then
      .cons p' (mulPow p m)
    else
      .cons { x := p.x, k := p.k + p'.k } m

def Mon.length : Mon → Nat
  | .leaf _ => 1
  | .cons _ m => 1 + length m

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
      | m₁, .leaf p => m₁.mulPow p
      | .leaf p, m₂ => m₂.mulPow p
      | .cons p₁ m₁, .cons p₂ m₂ =>
        bif p₁.varLt p₂ then
          .cons p₁ (go fuel m₁ (.cons p₂ m₂))
        else bif p₂.varLt p₁ then
          .cons p₂ (go fuel (.cons p₁ m₁) m₂)
        else
          .cons { x := p₁.x, k := p₁.k + p₂.k } (go fuel m₁ m₂)

def Mon.degree : Mon → Nat
  | .leaf p => p.k
  | .cons p m => p.k + degree m

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
  | .leaf p₁, .leaf p₂ => p₁.revlex p₂
  | .leaf p₁, .cons p₂ m₂ =>
    bif p₁.x.ble p₂.x  then
      .gt
    else
      revlexWF (.leaf p₁) m₂ |>.then .gt
  | .cons p₁ m₁, .leaf p₂ =>
    bif p₂.x.ble p₁.x then
      .lt
    else
      revlexWF m₁ (.leaf p₂) |>.then .lt
  | .cons p₁ m₁, .cons p₂ m₂ =>
    bif p₁.x == p₂.x then
      revlexWF m₁ m₂ |>.then (powerRevlex p₁.k p₂.k)
    else bif p₁.x.blt p₂.x then
      revlexWF m₁ (.cons p₂ m₂) |>.then .gt
    else
      revlexWF (.cons p₁ m₁) m₂ |>.then .lt

def Mon.revlexFuel (fuel : Nat) (m₁ m₂ : Mon) : Ordering :=
  match fuel with
  | 0 =>
    -- This branch is not reachable in practice, but we add it here
    -- to ensure we can prove helper theorems
    revlexWF m₁ m₂
  | fuel + 1 =>
    match m₁, m₂ with
    | .leaf p₁, .leaf p₂ => p₁.revlex p₂
    | .leaf p₁, .cons p₂ m₂ =>
      bif p₁.x.ble p₂.x  then
        .gt
      else
        revlexFuel fuel (.leaf p₁) m₂ |>.then .gt
    | .cons p₁ m₁, .leaf p₂ =>
      bif p₂.x.ble p₁.x then
        .lt
      else
        revlexFuel fuel m₁ (.leaf p₂) |>.then .lt
    | .cons p₁ m₁, .cons p₂ m₂ =>
      bif p₁.x == p₂.x then
        revlexFuel fuel m₁ m₂ |>.then (powerRevlex p₁.k p₂.k)
      else bif p₁.x.blt p₂.x then
        revlexFuel fuel m₁ (.cons p₂ m₂) |>.then .gt
      else
        revlexFuel fuel (.cons p₁ m₁) m₂ |>.then .lt

def Mon.revlex (m₁ m₂ : Mon) : Ordering :=
  revlexFuel hugeFuel m₁ m₂

def Mon.grevlex (m₁ m₂ : Mon) : Ordering :=
  compare m₁.degree m₂.degree |>.then (revlex m₁ m₂)

inductive Poly where
  | num (k : Int)
  | add (k : Int) (v : Mon) (p : Poly)
  deriving BEq

def Poly.denote [CommRing α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => Int.cast k
  | .add k m p => Int.cast k * m.denote ctx + denote ctx p

def Poly.addConst (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k' + k)
  | .add k' m p => .add k' m (addConst p k)

def Poly.insert (k : Int) (m : Mon) (p : Poly) : Poly :=
  match p with
  | .num k' => .add k m (.num k')
  | .add k' m' p =>
    match m.grevlex m' with
    | .eq =>
      let k'' := k + k'
      bif k'' == 0 then
        p
      else
        .add k'' m p
    | .lt => .add k m (.add k' m' p)
    | .gt => .add k' m' (insert k m p)

def Poly.concat (p₁ p₂ : Poly) : Poly :=
  match p₁ with
  | .num k₁ => p₂.addConst k₁
  | .add k m p₁ => .add k m (concat p₁ p₂)

def Poly.mulConst (k : Int) (p : Poly) : Poly :=
  bif k == 0 then
    .num 0
  else
    go p
where
  go : Poly → Poly
   | .num k' => .num (k*k')
   | .add k' m p => .add (k*k') m (go p)

def Poly.mulMon (k : Int) (m : Mon) (p : Poly) : Poly :=
  bif k == 0 then
    .num 0
  else
    go p
where
  go : Poly → Poly
   | .num k' => .add (k*k') m (.num 0)
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
        | .lt => .add k₁ m₁ (go fuel p₁ (.add k₂ m₂ p₂))
        | .gt => .add k₂ m₂ (go fuel (.add k₁ m₁ p₁) p₂)

theorem Power.denote_eq [CommRing α] (ctx : Context α) (p : Power)
    : p.denote ctx = p.x.denote ctx ^ p.k := by
  cases p <;> simp [Power.denote] <;> split <;> simp [pow_zero, pow_succ, one_mul]

theorem Mon.denote'_go_eq_denote [CommRing α] (ctx : Context α) (a : α) (m : Mon)
    : denote'.go ctx a m = a * denote ctx m := by
  induction m generalizing a <;> simp [Mon.denote, Mon.denote'.go]
  next p' m ih =>
    simp [Mon.denote] at ih
    rw [ih, mul_assoc]

theorem Mon.denote'_eq_denote [CommRing α] (ctx : Context α) (m : Mon)
    : denote' ctx m = denote ctx m := by
  cases m <;> simp [Mon.denote, Mon.denote']
  next p m => apply denote'_go_eq_denote

theorem Mon.denote_concat [CommRing α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (concat m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  induction m₁ <;> simp [concat, denote, *]
  next p₁ m₁ ih => rw [mul_assoc]

private theorem le_of_blt_false {a b : Nat} : a.blt b = false → b ≤ a := by
  intro h; apply Nat.le_of_not_gt; show ¬a < b
  rw [← Nat.blt_eq, h]; simp

private theorem eq_of_blt_false {a b : Nat} : a.blt b = false → b.blt a = false → a = b := by
  intro h₁ h₂
  replace h₁ := le_of_blt_false h₁
  replace h₂ := le_of_blt_false h₂
  exact Nat.le_antisymm h₂ h₁

theorem Mon.denote_mulPow [CommRing α] (ctx : Context α) (p : Power) (m : Mon)
    : denote ctx (mulPow p m) = p.denote ctx * m.denote ctx := by
  fun_induction mulPow <;> simp [mulPow, *]
  next => simp [denote]
  next => simp [denote]; rw [mul_comm]
  next p' h₁ h₂ =>
    have := eq_of_blt_false h₁ h₂
    simp [denote, Power.denote_eq, this, pow_add]
  next => simp [denote]
  next => simp [denote, mul_assoc, mul_comm, mul_left_comm, *]
  next h₁ h₂ =>
    have := eq_of_blt_false h₁ h₂
    simp [denote, Power.denote_eq, pow_add, this, mul_assoc]

theorem Mon.denote_mul [CommRing α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (mul m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  unfold mul
  generalize hugeFuel = fuel
  fun_induction mul.go <;> simp [mul.go, denote, denote_concat, denote_mulPow, *]
  next => rw [mul_comm]
  next => simp [mul_assoc]
  next => simp [mul_assoc, mul_left_comm, mul_comm]
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
  next => apply Power.eq_of_revlex
  next p₁ m₁ p₂ m₂ h ih =>
    cases p₁; cases p₂; intro h₁ h₂; simp [ih h₁, h]
    simp at h h₂
    simp [h, eq_of_powerRevlex h₂]

theorem Mon.eq_of_revlexFuel {fuel : Nat} {m₁ m₂ : Mon} : revlexFuel fuel m₁ m₂ = .eq → m₁ = m₂ := by
  fun_induction revlexFuel <;> simp [revlexFuel, *, then_gt, then_lt, then_eq]
  next => apply eq_of_revlexWF
  next => apply Power.eq_of_revlex
  next p₁ m₁ p₂ m₂ h ih =>
    cases p₁; cases p₂; intro h₁ h₂; simp [ih h₁, h]
    simp at h h₂
    simp [h, eq_of_powerRevlex h₂]

theorem Mon.eq_of_revlex {m₁ m₂ : Mon} : revlex m₁ m₂ = .eq → m₁ = m₂ := by
  apply eq_of_revlexFuel

theorem Mon.eq_of_grevlex {m₁ m₂ : Mon} : grevlex m₁ m₂ = .eq → m₁ = m₂ := by
  simp [grevlex, then_eq]; intro; apply eq_of_revlex

theorem Poly.denote_addConst [CommRing α] (ctx : Context α) (p : Poly) (k : Int) : (addConst p k).denote ctx = p.denote ctx + k := by
  fun_induction addConst <;> simp [addConst, denote, *]
  next => rw [intCast_add]
  next => simp [add_comm, add_left_comm, add_assoc]

theorem Poly.denote_insert [CommRing α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (insert k m p).denote ctx = k * m.denote ctx + p.denote ctx := by
  fun_induction insert <;> simp_all +zetaDelta [insert, denote, cond_eq_if]
  next h₁ _ h₂ =>
    rw [← add_assoc, Mon.eq_of_grevlex h₁, ← right_distrib, ← intCast_add, h₂, intCast_zero, zero_mul, zero_add]
  next h₁ _ _ =>
    rw [intCast_add, right_distrib, add_assoc, Mon.eq_of_grevlex h₁]
  next =>
    rw [add_left_comm]

theorem Poly.denote_concat [CommRing α] (ctx : Context α) (p₁ p₂ : Poly)
    : (concat p₁ p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  fun_induction concat <;> simp [concat, *, denote_addConst, denote]
  next => rw [add_comm]
  next => rw [add_assoc]

theorem Poly.denote_mulConst [CommRing α] (ctx : Context α) (k : Int) (p : Poly)
    : (mulConst k p).denote ctx = k * p.denote ctx := by
  simp [mulConst, cond_eq_if] <;> split
  next => simp [denote, *, intCast_zero, zero_mul]
  next =>
    fun_induction mulConst.go <;> simp [mulConst.go, denote, *]
    next => rw [intCast_mul]
    next => rw [intCast_mul, left_distrib, mul_assoc]

theorem Poly.denote_mulMon [CommRing α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : (mulMon k m p).denote ctx = k * m.denote ctx * p.denote ctx := by
  simp [mulMon, cond_eq_if] <;> split
  next => simp [denote, *, intCast_zero, zero_mul]
  next =>
    fun_induction mulMon.go <;> simp [mulMon.go, denote, *]
    next => simp [intCast_mul, intCast_zero, add_zero, mul_comm, mul_left_comm, mul_assoc]
    next => simp [Mon.denote_mul, intCast_mul, left_distrib, mul_comm, mul_left_comm, mul_assoc]

theorem Poly.denote_combine [CommRing α] (ctx : Context α) (p₁ p₂ : Poly)
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

end CommRing
end Lean.Grind
