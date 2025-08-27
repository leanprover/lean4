/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Core
public import Init.Data.Nat.Lemmas
public import Init.Data.RArray
public import Init.Data.Bool
@[expose] public section

namespace Lean.Grind.AC
abbrev Var := Nat

structure Context (α : Sort u) where
  vars    : RArray (PLift α)
  op      : α → α → α

inductive Expr where
  | var (x : Var)
  | op (lhs rhs : Expr)
  deriving Inhabited, Repr, BEq

noncomputable def Var.denote {α : Sort u} (ctx : Context α) (x : Var) : α :=
  PLift.rec (fun x => x) (ctx.vars.get x)

noncomputable def Expr.denote {α} (ctx : Context α) (e : Expr) : α :=
  Expr.rec (fun x => x.denote ctx) (fun _ _ ih₁ ih₂ => ctx.op ih₁ ih₂) e

theorem Expr.denote_var {α} (ctx : Context α) (x : Var) : (Expr.var x).denote ctx = x.denote ctx := rfl
theorem Expr.denote_op {α} (ctx : Context α) (a b : Expr) : (Expr.op a b).denote ctx = ctx.op (a.denote ctx) (b.denote ctx) := rfl

attribute [local simp] Expr.denote_var Expr.denote_op

inductive Seq where
  | var (x : Var)
  | cons (x : Var) (s : Seq)
  deriving Inhabited, Repr, BEq

-- Kernel version for Seq.beq
noncomputable def Seq.beq' (s₁ : Seq) : Seq → Bool :=
  Seq.rec
    (fun x s₂ => Seq.rec (fun y => Nat.beq x y) (fun _ _ _ => false) s₂)
    (fun x _ ih s₂ => Seq.rec (fun _ => false) (fun y s₂ _ => Bool.and' (Nat.beq x y) (ih s₂)) s₂)
    s₁

theorem Seq.beq'_eq (s₁ s₂ : Seq) : s₁.beq' s₂ = (s₁ = s₂) := by
  induction s₁ generalizing s₂ <;> cases s₂ <;> simp [beq']
  rename_i x₁ _ ih _ s₂
  intro; subst x₁
  simp [← ih s₂, ← Bool.and'_eq_and]; rfl

attribute [local simp] Seq.beq'_eq

instance : LawfulBEq Seq where
  eq_of_beq {a} := by
    induction a <;> intro b <;> cases b <;> simp! [BEq.beq]
    next x₁ s₁ ih x₂ s₂ => intro h₁ h₂; simp [h₁, ih h₂]
  rfl := by intro a; induction a <;> simp! [BEq.beq]; assumption

noncomputable def Seq.denote {α} (ctx : Context α) (s : Seq) : α :=
  Seq.rec (fun x => x.denote ctx) (fun x _ ih => ctx.op (x.denote ctx) ih) s

theorem Seq.denote_var {α} (ctx : Context α) (x : Var) : (Seq.var x).denote ctx = x.denote ctx := rfl
theorem Seq.denote_op {α} (ctx : Context α) (x : Var) (s : Seq) : (Seq.cons x s).denote ctx = ctx.op (x.denote ctx) (s.denote ctx) := rfl

attribute [local simp] Seq.denote_var Seq.denote_op

def Expr.toSeq' (e : Expr) (s : Seq) : Seq :=
  match e with
  | .var x => .cons x s
  | .op a b => toSeq' a (toSeq' b s)

-- Kernel version for `toSeq'`
noncomputable def Expr.toSeq'_k (e : Expr) : Seq → Seq :=
  Expr.rec .cons (fun _ _ iha ihb s => iha (ihb s)) e

theorem Expr.toSeq'_k_eq_toSeq' (e : Expr) (s : Seq) : toSeq'_k e s = toSeq' e s := by
  fun_induction toSeq' e s
  next => rfl
  next a b iha ihb => rw [← ihb, ← iha, toSeq'_k]; rfl

def Expr.toSeq (e : Expr) : Seq :=
  match e with
  | .var x  => .var x
  | .op a b => toSeq' a (toSeq b)

-- Kernel version for `toSeq`
noncomputable def Expr.toSeq_k (e : Expr) : Seq :=
  Expr.rec .var (fun a _ _ ihb => toSeq'_k a ihb) e

theorem Expr.toSeq_k_eq_toSeq (e : Expr) : toSeq_k e = toSeq e := by
  fun_induction toSeq e
  next => rfl
  next a b ih => rw [← ih, ← Expr.toSeq'_k_eq_toSeq', Expr.toSeq_k]; rfl

attribute [local simp] Expr.toSeq'_k_eq_toSeq' Expr.toSeq_k_eq_toSeq

theorem Expr.denote_toSeq' {α} (ctx : Context α) {_ : Std.Associative ctx.op} (e : Expr) (s : Seq)
    : (toSeq' e s).denote ctx = ctx.op (e.denote ctx) (s.denote ctx) := by
  fun_induction toSeq' e s
  next => simp
  next a b s iha ihb => simp [*, Std.Associative.assoc]

attribute [local simp] Expr.denote_toSeq'

theorem Expr.denote_toSeq {α} (ctx : Context α) {_ : Std.Associative ctx.op} (e : Expr)
    : e.toSeq.denote ctx = e.denote ctx := by
  fun_induction toSeq e
  next => simp
  next a b ih => simp [*]

attribute [local simp] Expr.denote_toSeq

def Seq.erase0 (s : Seq) : Seq :=
  match s with
  | .var x => .var x
  | .cons x s =>
    let s' := erase0 s
    if x == 0 then
      s'
    else if s' == .var 0 then
      .var x
    else
      .cons x s'

-- Kernel version for `erase0`
noncomputable def Seq.erase0_k (s : Seq) : Seq :=
  Seq.rec (fun x => .var x) (fun x _ ih => Bool.rec (Bool.rec (.cons x ih) (.var x) (Seq.beq' ih (.var 0))) ih (Nat.beq x 0)) s

theorem Seq.erase0_k_var (x : Var)
    : (Seq.var x).erase0_k = .var x :=
  rfl

theorem Seq.erase0_k_cons (x : Var) (s : Seq)
    : (Seq.cons x s).erase0_k = Bool.rec (Bool.rec (.cons x s.erase0_k) (.var x) (Seq.beq' s.erase0_k (.var 0))) s.erase0_k (Nat.beq x 0) :=
  rfl

attribute [local simp] Seq.erase0_k_var Seq.erase0_k_cons

theorem Seq.erase0_k_eq_erase0 (s : Seq) : s.erase0_k = s.erase0 := by
  fun_induction erase0 s <;> simp
  next h ih => simp at h; simp +zetaDelta; simp [← ih, h]
  next x _ _ h₁ h₂ ih =>
    replace h₁ : Nat.beq x 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; simp at h₁; assumption
    simp +zetaDelta [← Seq.beq'_eq, ← ih] at h₂
    simp [h₁, h₂]
  next x _ _ h₁ h₂ ih =>
    replace h₁ : Nat.beq x 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; simp at h₁; assumption
    simp +zetaDelta [← Seq.beq'_eq, ← ih] at h₂
    simp +zetaDelta [h₁, h₂, ← ih]

attribute [local simp] Seq.erase0_k_eq_erase0

theorem Seq.denote_erase0 {α} (ctx : Context α) {inst : Std.LawfulIdentity ctx.op (Var.denote ctx 0)} (s : Seq)
    : s.erase0.denote ctx = s.denote ctx := by
  fun_induction erase0 s <;> simp_all +zetaDelta
  next => rw [Std.LawfulLeftIdentity.left_id (self := inst.toLawfulLeftIdentity)]
  next => rw [Std.LawfulRightIdentity.right_id (self := inst.toLawfulRightIdentity)]

attribute [local simp] Seq.denote_erase0

def Seq.insert (x : Var) (s : Seq) : Seq :=
  match s with
  | .var y => if Nat.blt x y then .cons x (.var y) else .cons y (.var x)
  | .cons y s => if Nat.blt x y then .cons x (.cons y s) else .cons y (insert x s)

-- Kernel version for `insert`
noncomputable def Seq.insert_k (x : Var) (s : Seq) : Seq :=
  Seq.rec
    (fun y => Bool.rec (.cons y (.var x)) (.cons x (.var y)) (Nat.blt x y))
    (fun y s ih => Bool.rec (.cons y ih) (.cons x (.cons y s)) (Nat.blt x y))
    s

theorem Seq.insert_k_eq_insert (x : Var) (s : Seq) : insert_k x s = insert x s := by
  fun_induction insert x s <;> simp [insert_k, *]
  next ih => simp [← ih]; rfl

attribute [local simp] Seq.insert_k_eq_insert

theorem Seq.denote_insert {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op} (x : Var) (s : Seq)
    : (s.insert x).denote ctx = ctx.op (x.denote ctx) (s.denote ctx) := by
  fun_induction insert x s <;> simp
  next => rw [Std.Commutative.comm (self := inst₂)]
  next y s h ih =>
    simp [ih, ← Std.Associative.assoc (self := inst₁)]
    rw [Std.Commutative.comm (self := inst₂) (x.denote ctx)]

attribute [local simp] Seq.denote_insert

def Seq.sort' (s : Seq) (acc : Seq) : Seq :=
  match s with
  | .var x => acc.insert x
  | .cons x s => sort' s (acc.insert x)

-- Kernel version for `sort'`
noncomputable def Seq.sort'_k (s : Seq) : Seq → Seq :=
  Seq.rec (fun x acc => acc.insert x) (fun x _ ih acc => ih (acc.insert x)) s

theorem Seq.sort'_k_eq_sort' (s acc : Seq) : sort'_k s acc = sort' s acc := by
  induction s generalizing acc <;> simp [sort', sort'_k]
  next ih => simp [← ih]; rfl

attribute [local simp] Seq.sort'_k_eq_sort'

theorem Seq.denote_sort' {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op} (s acc : Seq)
    : (sort' s acc).denote ctx = ctx.op (s.denote ctx) (acc.denote ctx) := by
  fun_induction sort' s acc <;> simp
  next x s ih =>
    simp [ih, ← Std.Associative.assoc (self := inst₁)]
    rw [Std.Commutative.comm (self := inst₂) (x.denote ctx) (s.denote ctx)]

attribute [local simp] Seq.denote_sort'

def Seq.sort (s : Seq) : Seq :=
  match s with
  | .var x => .var x
  | .cons x s => sort' s (.var x)

-- Kernel version for `sort`
noncomputable def Seq.sort_k (s : Seq) : Seq :=
  Seq.rec (fun x => .var x) (fun x s _ => sort' s (.var x)) s

theorem Seq.sort_k_eq_sort (s : Seq) : s.sort_k = s.sort := by
  cases s <;> simp [sort, sort_k]

attribute [local simp] Seq.sort_k_eq_sort

theorem Seq.denote_sort {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op} (s : Seq)
    : s.sort.denote ctx = s.denote ctx := by
  cases s <;> simp [sort]
  rw [Std.Commutative.comm (self := inst₂)]

attribute [local simp] Seq.denote_sort

def Seq.eraseDup (s : Seq) : Seq :=
  match s with
  | .var x => .var x
  | .cons x s =>
    let s' := s.eraseDup
    match s' with
    | .var y => if Nat.beq x y then .var x else .cons x (.var y)
    | .cons y s' => if Nat.beq x y then .cons y s' else .cons x (.cons y s')

-- Kernel version for `eraseDup`
noncomputable def Seq.eraseDup_k (s : Seq) : Seq :=
  Seq.rec (fun x => .var x)
    (fun x _ ih => Seq.rec
      (fun y => Bool.rec (.cons x (.var y)) (.var x) (Nat.beq x y))
      (fun y s' _ => Bool.rec (.cons x (.cons y s')) (.cons y s') (Nat.beq x y)) ih)
    s

theorem Seq.eraseDup_k_cons (x : Var) (s : Seq)
    : (Seq.cons x s).eraseDup_k =
      Seq.rec
        (fun y => Bool.rec (.cons x (.var y)) (.var x) (Nat.beq x y))
        (fun y s' _ => Bool.rec (.cons x (.cons y s')) (.cons y s') (Nat.beq x y)) s.eraseDup_k :=
  rfl

attribute [local simp] Seq.eraseDup_k_cons

theorem Seq.eraseDup_k_eq_eraseDup (s : Seq) : s.eraseDup_k = s.eraseDup := by
  induction s <;> simp [eraseDup]
  next => simp [eraseDup_k]
  split <;> split <;> simp [*]
  all_goals rename_i h; rw [← Nat.beq_eq, Bool.not_eq_true] at h; simp [h]

attribute [local simp] Seq.eraseDup_k_eq_eraseDup

-- theorem Seq.denote_eraseDup {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.IdempotentOp ctx.op} (s : Seq)
--    : s.eraseDup.denote ctx = s.denote ctx := by
--   fun_induction eraseDup s -- FAILED

theorem Seq.denote_eraseDup {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.IdempotentOp ctx.op} (s : Seq)
    : s.eraseDup.denote ctx = s.denote ctx := by
  induction s <;> simp [eraseDup] <;> split <;> split
  next ih _ _ h₁ h₂ => simp [← ih, h₁, h₂, Std.IdempotentOp.idempotent]
  next ih _ _ h₁ _ => simp [← ih, h₁]
  next ih _ _ _ h₁ h₂ => simp [← ih, h₁, h₂, ← Std.Associative.assoc (self := inst₁), Std.IdempotentOp.idempotent]
  next ih _ _ _ h₁ _ => simp [← ih, h₁]

attribute [local simp] Seq.denote_eraseDup

def Seq.concat (s₁ s₂ : Seq) : Seq :=
  match s₁ with
  | .var x => .cons x s₂
  | .cons x s => .cons x (concat s s₂)

-- Kernel version for `concat`
noncomputable def Seq.concat_k (s₁ : Seq) : Seq → Seq :=
  Seq.rec (fun x s₂ => .cons x s₂) (fun x _ ih s₂ => .cons x (ih s₂)) s₁

theorem Seq.concat_k_eq_concat (s₁ s₂ : Seq) : concat_k s₁ s₂ = concat s₁ s₂ := by
  fun_induction concat s₁ s₂ <;> simp [concat_k]
  next ih => simp [← ih]; rfl

attribute [local simp] Seq.concat_k_eq_concat

theorem Seq.denote_concat {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} (s₁ s₂ : Seq)
    : (s₁.concat s₂).denote ctx = ctx.op (s₁.denote ctx) (s₂.denote ctx) := by
  fun_induction concat <;> simp [*, Std.Associative.assoc (self := inst₁)]

attribute [local simp] Seq.denote_concat

noncomputable def simp_prefix_cert (lhs rhs tail s s' : Seq) : Bool :=
  s.beq' (lhs.concat_k tail) |>.and' (s'.beq' (rhs.concat_k tail))

/--
Given `lhs = rhs`, and a term `s := lhs * tail`, rewrite it to `s' := rhs * tail`
-/
theorem simp_prefix {α} (ctx : Context α) {_ : Std.Associative ctx.op} (lhs rhs tail s s' : Seq)
    : simp_prefix_cert lhs rhs tail s s' → lhs.denote ctx = rhs.denote ctx → s.denote ctx = s'.denote ctx := by
  simp [simp_prefix_cert]; intro _ _ h; subst s s'; simp [h]

noncomputable def simp_suffix_cert (lhs rhs head s s' : Seq) : Bool :=
  s.beq' (head.concat_k lhs) |>.and' (s'.beq' (head.concat_k rhs))

/--
Given `lhs = rhs`, and a term `s := head * lhs`, rewrite it to `s' := head * rhs`
-/
theorem simp_suffix {α} (ctx : Context α) {_ : Std.Associative ctx.op} (lhs rhs head s s' : Seq)
    : simp_suffix_cert lhs rhs head s s' → lhs.denote ctx = rhs.denote ctx → s.denote ctx = s'.denote ctx := by
  simp [simp_suffix_cert]; intro _ _ h; subst s s'; simp [h]

noncomputable def simp_middle_cert (lhs rhs head tail s s' : Seq) : Bool :=
  s.beq' (head.concat_k (lhs.concat_k tail)) |>.and' (s'.beq' (head.concat_k (rhs.concat_k tail)))

/--
Given `lhs = rhs`, and a term `s := head * lhs * tail`, rewrite it to `s' := head * rhs * tail`
-/
theorem simp_middle {α} (ctx : Context α) {_ : Std.Associative ctx.op} (lhs rhs head tail s s' : Seq)
    : simp_middle_cert lhs rhs head tail s s' → lhs.denote ctx = rhs.denote ctx → s.denote ctx = s'.denote ctx := by
  simp [simp_middle_cert]; intro _ _ h; subst s s'; simp [h]

noncomputable def superpose_prefix_suffix_cert (p c s lhs₁ rhs₁ lhs₂ rhs₂ lhs rhs : Seq) : Bool :=
  lhs₁.beq' (p.concat_k c) |>.and'
  (lhs₂.beq' (c.concat_k s)) |>.and'
  (lhs.beq' (rhs₁.concat_k s)) |>.and'
  (rhs.beq' (p.concat_k rhs₂))

/--
Given `lhs₁ = rhs₁` and `lhs₂ = rhs₂` where `lhs₁ := p * c` and `lhs₂ := c * s`,
`lhs = rhs` where `lhs := rhs₁ * s` and `rhs := p * rhs₂`
-/
theorem superpose_prefix_suffix {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} (p c s lhs₁ rhs₁ lhs₂ rhs₂ lhs rhs : Seq)
    : superpose_prefix_suffix_cert p c s lhs₁ rhs₁ lhs₂ rhs₂ lhs rhs → lhs₁.denote ctx = rhs₁.denote ctx → lhs₂.denote ctx = rhs₂.denote ctx
      → lhs.denote ctx = rhs.denote ctx := by
  simp [superpose_prefix_suffix_cert]; intro _ _ _ _; subst lhs₁ lhs₂ lhs rhs; simp
  intro h₁ h₂; simp [← h₁, ← h₂, Std.Associative.assoc (self := inst₁)]

def Seq.combineFuel (fuel : Nat) (s₁ s₂ : Seq) : Seq :=
  match fuel with
  | 0 => s₁.concat s₂
  | fuel + 1 =>
    match s₁, s₂ with
    | .var x₁, .var x₂  => if Nat.blt x₁ x₂ then .cons x₁ (.var x₂) else .cons x₂ (.var x₁)
    | .var x₁, .cons .. => s₂.insert x₁
    | .cons .., .var x₂ => s₁.insert x₂
    | .cons x₁ s₁, .cons x₂ s₂ =>
      if Nat.blt x₁ x₂ then
        .cons x₁ (combineFuel fuel s₁ (.cons x₂ s₂))
      else
        .cons x₂ (combineFuel fuel (.cons x₁ s₁) s₂)

-- Kernel version for `combineFuel`
noncomputable def Seq.combineFuel_k (fuel : Nat) : Seq → Seq → Seq :=
  Nat.rec concat
    (fun _ ih s₁ s₂ => Seq.rec
      (fun x₁ => Seq.rec (fun x₂ => Bool.rec (.cons x₂ (.var x₁)) (.cons x₁ (.var x₂)) (Nat.blt x₁ x₂)) (fun _ _ _ => s₂.insert x₁) s₂)
      (fun x₁ s₁' _ => Seq.rec (fun x₂ => s₁.insert x₂)
        (fun x₂ s₂' _ => Bool.rec (.cons x₂ (ih s₁ s₂')) (.cons x₁ (ih s₁' s₂)) (Nat.blt x₁ x₂)) s₂)
      s₁) fuel

theorem Seq.combineFuel_k_eq_combineFuel (fuel : Nat) (s₁ s₂ : Seq) : combineFuel_k fuel s₁ s₂ = combineFuel fuel s₁ s₂ := by
  fun_induction combineFuel <;> simp [combineFuel_k, *]
  next => rfl
  next ih => rw [← ih]; rfl
  next ih => rw [← ih]; rfl

attribute [local simp] Seq.combineFuel_k_eq_combineFuel

theorem Seq.denote_combineFuel {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op} (fuel : Nat) (s₁ s₂ : Seq)
    : (s₁.combineFuel fuel s₂).denote ctx = ctx.op (s₁.denote ctx) (s₂.denote ctx) := by
  fun_induction combineFuel <;> simp
  next => simp [Std.Commutative.comm (self := inst₂)]
  next => simp [Std.Commutative.comm (self := inst₂)]
  next ih => simp [ih, Std.Associative.assoc (self := inst₁)]
  next x₁ s₁ x₂ s₂ h ih =>
    simp [ih]
    rw [← Std.Associative.assoc (self := inst₁), ← Std.Associative.assoc (self := inst₁), Std.Commutative.comm (self := inst₂) (x₂.denote ctx)]
    rw [Std.Associative.assoc (self := inst₁), Std.Associative.assoc (self := inst₁), Std.Associative.assoc (self := inst₁) (x₁.denote ctx)]
    apply congrArg (ctx.op (x₁.denote ctx))
    rw [← Std.Associative.assoc (self := inst₁), ← Std.Associative.assoc (self := inst₁) (s₁.denote ctx)]
    rw [Std.Commutative.comm (self := inst₂) (x₂.denote ctx)]

attribute [local simp] Seq.denote_combineFuel

def hugeFuel := 1000000

def Seq.combine (s₁ s₂ : Seq) : Seq :=
  combineFuel hugeFuel s₁ s₂

noncomputable def Seq.combine_k (s₁ s₂ : Seq) : Seq :=
  combineFuel_k hugeFuel s₁ s₂

theorem Seq.combine_k_eq_combine (s₁ s₂ : Seq) : s₁.combine_k s₂ = s₁.combine s₂ := by
  simp [combine, combine_k]

attribute [local simp] Seq.combine_k_eq_combine

theorem Seq.denote_combine {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op} (s₁ s₂ : Seq)
    : (s₁.combine s₂).denote ctx = ctx.op (s₁.denote ctx) (s₂.denote ctx) := by
  simp [combine]

attribute [local simp] Seq.denote_combine

noncomputable def simp_ac_cert (c lhs rhs s s' : Seq) : Bool :=
  s.beq' (c.combine_k lhs) |>.and'
  (s'.beq' (c.combine_k rhs))

/--
Given `lhs = rhs`, and a term `s := combine a lhs`, rewrite it to `s' := combine a rhs`
-/
theorem simp_ac {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op} (c lhs rhs s s' : Seq)
    : simp_ac_cert c lhs rhs s s' → lhs.denote ctx = rhs.denote ctx → s.denote ctx = s'.denote ctx := by
  simp [simp_ac_cert]; intro _ _; subst s s'; simp; intro h; rw [h]

noncomputable def superpose_ac_cert (a b c lhs₁ rhs₁ lhs₂ rhs₂ lhs rhs : Seq) : Bool :=
  lhs₁.beq' (c.combine_k a) |>.and'
  (lhs₂.beq' (c.combine_k b)) |>.and'
  (lhs.beq' (b.combine_k rhs₁)) |>.and'
  (rhs.beq' (a.combine_k rhs₂))

/--
Given `lhs₁ = rhs₁` and `lhs₂ = rhs₂` where `lhs₁ := combine c a` and `lhs₂ := combine c b`,
`lhs = rhs` where `lhs := combine b rhs₁` and `rhs := combine a rhs₂`
-/
theorem superpose_ac {α} (ctx : Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op}  (a b c lhs₁ rhs₁ lhs₂ rhs₂ lhs rhs : Seq)
    : superpose_ac_cert a b c lhs₁ rhs₁ lhs₂ rhs₂ lhs rhs → lhs₁.denote ctx = rhs₁.denote ctx → lhs₂.denote ctx = rhs₂.denote ctx
      → lhs.denote ctx = rhs.denote ctx := by
  simp [superpose_ac_cert]; intro _ _ _ _; subst lhs₁ lhs₂ lhs rhs; simp
  intro h₁ h₂; simp [← h₁, ← h₂]
  rw [← Std.Associative.assoc (self := inst₁), Std.Commutative.comm (self := inst₂) (b.denote ctx)]
  rw [← Std.Associative.assoc (self := inst₁), Std.Commutative.comm (self := inst₂) (a.denote ctx)]
  simp [Std.Associative.assoc (self := inst₁)]
  apply congrArg (ctx.op (c.denote ctx))
  rw [Std.Commutative.comm (self := inst₂) (b.denote ctx)]

noncomputable def eq_norm_a_cert (lhs rhs : Expr) (lhs' rhs' : Seq) : Bool :=
  lhs.toSeq.beq' lhs' |>.and' (rhs.toSeq.beq' rhs')

theorem eq_norm_a {α} (ctx : Context α) {_ : Std.Associative ctx.op} (lhs rhs : Expr) (lhs' rhs' : Seq)
    : eq_norm_a_cert lhs rhs lhs' rhs' → lhs.denote ctx = rhs.denote ctx → lhs'.denote ctx = rhs'.denote ctx := by
  simp [eq_norm_a_cert]; intro _ _; subst lhs' rhs'; simp

noncomputable def eq_norm_ac_cert (lhs rhs : Expr) (lhs' rhs' : Seq) : Bool :=
  lhs.toSeq.sort.beq' lhs' |>.and' (rhs.toSeq.sort.beq' rhs')

theorem eq_norm_ac {α} (ctx : Context α) {_ : Std.Associative ctx.op} {_ : Std.Commutative ctx.op} (lhs rhs : Expr) (lhs' rhs' : Seq)
    : eq_norm_ac_cert lhs rhs lhs' rhs' → lhs.denote ctx = rhs.denote ctx → lhs'.denote ctx = rhs'.denote ctx := by
  simp [eq_norm_ac_cert]; intro _ _; subst lhs' rhs'; simp

noncomputable def eq_norm_ai_cert (lhs rhs : Expr) (lhs' rhs' : Seq) : Bool :=
  lhs.toSeq.erase0.beq' lhs' |>.and' (rhs.toSeq.erase0.beq' rhs')

theorem eq_norm_ai {α} (ctx : Context α) {_ : Std.Associative ctx.op} {_ : Std.LawfulIdentity ctx.op (Var.denote ctx 0)}
      (lhs rhs : Expr) (lhs' rhs' : Seq) : eq_norm_ai_cert lhs rhs lhs' rhs' → lhs.denote ctx = rhs.denote ctx → lhs'.denote ctx = rhs'.denote ctx := by
  simp [eq_norm_ai_cert]; intro _ _; subst lhs' rhs'; simp

noncomputable def eq_norm_aci_cert (lhs rhs : Expr) (lhs' rhs' : Seq) : Bool :=
  lhs.toSeq.erase0.sort.beq' lhs' |>.and' (rhs.toSeq.erase0.sort.beq' rhs')

theorem eq_norm_aci {α} (ctx : Context α) {_ : Std.Associative ctx.op} {_ : Std.Commutative ctx.op} {_ : Std.LawfulIdentity ctx.op (Var.denote ctx 0)}
      (lhs rhs : Expr) (lhs' rhs' : Seq) : eq_norm_aci_cert lhs rhs lhs' rhs' → lhs.denote ctx = rhs.denote ctx → lhs'.denote ctx = rhs'.denote ctx := by
  simp [eq_norm_aci_cert]; intro _ _; subst lhs' rhs'; simp

noncomputable def eq_erase_dup_cert (lhs rhs lhs' rhs' : Seq) : Bool :=
  lhs.eraseDup.beq' lhs' |>.and' (rhs.eraseDup.beq' rhs')

theorem eq_erase_dup {α} (ctx : Context α) {_ : Std.Associative ctx.op} {_ : Std.IdempotentOp ctx.op}
      (lhs rhs lhs' rhs' : Seq) : eq_erase_dup_cert lhs rhs lhs' rhs' → lhs.denote ctx = rhs.denote ctx → lhs'.denote ctx = rhs'.denote ctx := by
  simp [eq_erase_dup_cert]; intro _ _; subst lhs' rhs'; simp

theorem diseq_norm_a {α} (ctx : Context α) {_ : Std.Associative ctx.op} (lhs rhs : Expr) (lhs' rhs' : Seq)
    : eq_norm_a_cert lhs rhs lhs' rhs' → lhs.denote ctx ≠ rhs.denote ctx → lhs'.denote ctx ≠ rhs'.denote ctx := by
  simp [eq_norm_a_cert]; intro _ _; subst lhs' rhs'; simp

theorem diseq_norm_ac {α} (ctx : Context α) {_ : Std.Associative ctx.op} {_ : Std.Commutative ctx.op} (lhs rhs : Expr) (lhs' rhs' : Seq)
    : eq_norm_ac_cert lhs rhs lhs' rhs' → lhs.denote ctx ≠ rhs.denote ctx → lhs'.denote ctx ≠ rhs'.denote ctx := by
  simp [eq_norm_ac_cert]; intro _ _; subst lhs' rhs'; simp

theorem diseq_norm_ai {α} (ctx : Context α) {_ : Std.Associative ctx.op} {_ : Std.LawfulIdentity ctx.op (Var.denote ctx 0)}
      (lhs rhs : Expr) (lhs' rhs' : Seq) : eq_norm_ai_cert lhs rhs lhs' rhs' → lhs.denote ctx ≠ rhs.denote ctx → lhs'.denote ctx ≠ rhs'.denote ctx := by
  simp [eq_norm_ai_cert]; intro _ _; subst lhs' rhs'; simp

theorem diseq_norm_aci {α} (ctx : Context α) {_ : Std.Associative ctx.op} {_ : Std.Commutative ctx.op} {_ : Std.LawfulIdentity ctx.op (Var.denote ctx 0)}
      (lhs rhs : Expr) (lhs' rhs' : Seq) : eq_norm_aci_cert lhs rhs lhs' rhs' → lhs.denote ctx ≠ rhs.denote ctx → lhs'.denote ctx ≠ rhs'.denote ctx := by
  simp [eq_norm_aci_cert]; intro _ _; subst lhs' rhs'; simp

theorem diseq_erase_dup {α} (ctx : Context α) {_ : Std.Associative ctx.op} {_ : Std.IdempotentOp ctx.op}
      (lhs rhs lhs' rhs' : Seq) : eq_erase_dup_cert lhs rhs lhs' rhs' → lhs.denote ctx ≠ rhs.denote ctx → lhs'.denote ctx ≠ rhs'.denote ctx := by
  simp [eq_erase_dup_cert]; intro _ _; subst lhs' rhs'; simp

noncomputable def diseq_unsat_cert (lhs rhs : Seq) : Bool :=
  lhs.beq' rhs

theorem diseq_unsat {α} (ctx : Context α) (lhs rhs : Seq) : diseq_unsat_cert lhs rhs → lhs.denote ctx ≠ rhs.denote ctx → False := by
  simp [diseq_unsat_cert]; intro; subst lhs; simp

end Lean.Grind.AC
