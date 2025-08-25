/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kim Morrison
-/
module

prelude
public import Init.Grind.Ring.Basic
public import Init.Grind.Ordered.Ring
public import Init.Data.AC
import all Init.Data.AC

@[expose] public section

open Std

namespace Lean.Grind.Ring

namespace OfSemiring
variable (α : Type u)
attribute [local instance] Semiring.natCast Ring.intCast
variable [Semiring α]

-- Helper instance for `ac_rfl`
local instance : Std.Associative (· + · : α → α → α) where
  assoc := Semiring.add_assoc
local instance : Std.Commutative (· + · : α → α → α) where
  comm := Semiring.add_comm
local instance : Std.Associative (· * · : α → α → α) where
  assoc := Semiring.mul_assoc

@[local simp] private theorem exists_true : ∃ (_ : α), True := ⟨0, trivial⟩

@[local simp] def r : (α × α) → (α × α) → Prop
  | (a, b), (c, d) => ∃ k, a + d + k = b + c + k

def Q := Quot (r α)

variable {α}

theorem r_rfl (a : α × α) : r α a a := by
  cases a; refine ⟨0, ?_⟩; simp [Semiring.add_comm]

theorem r_sym {a b : α × α} : r α a b → r α b a := by
  cases a; cases b; simp [r]; intro h w; refine ⟨h, ?_⟩; simp [w, Semiring.add_comm]

theorem r_trans {a b c : α × α} : r α a b → r α b c → r α a c := by
  obtain ⟨a₁, a₂⟩ := a; obtain ⟨b₁, b₂⟩ := b; obtain ⟨c₁, c₂⟩ := c
  simp [r]
  intro k₁ h₁ k₂ h₂
  refine ⟨(k₁ + k₂ + b₁ + b₂), ?_⟩
  replace h₁ := congrArg (· + (b₁ + c₂ + k₂)) h₁; simp at h₁
  have haux₁ : a₁ + b₂ + k₁ + (b₁ + c₂ + k₂) = (a₁ + c₂) + (k₁ + k₂ + b₁ + b₂) := by ac_rfl
  have haux₂ : a₂ + b₁ + k₁ + (b₁ + c₂ + k₂) = (a₂ + c₁) + (k₁ + k₂ + b₁ + b₂) := by rw [h₂]; ac_rfl
  rw [haux₁, haux₂] at h₁
  exact h₁

theorem mul_helper {α} [Semiring α]
    {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ k₁ k₂ : α}
    (h₁ : a₁ + b₃ + k₁ = b₁ + a₃ + k₁)
    (h₂ : a₂ + b₄ + k₂ = b₂ + a₄ + k₂)
    : ∃ k, (a₁ * a₂ + b₁ * b₂) + (a₃ * b₄ + b₃ * a₄) + k = (a₁ * b₂ + b₁ * a₂) + (a₃ * a₄ + b₃ * b₄) + k := by
  refine ⟨b₃ * a₂ + k₁ * a₂ + a₃ * b₄ + a₃ * k₂ + k₁ * b₂ + b₃ * k₂, ?_⟩
  have h := congrArg (· * a₂) h₁
  simp [Semiring.right_distrib] at h
  have : a₁ * a₂ + b₁ * b₂ + (a₃ * b₄ + b₃ * a₄) + (b₃ * a₂ + k₁ * a₂ + a₃ * b₄ + a₃ * k₂ + k₁ * b₂ + b₃ * k₂) =
         a₁ * a₂ + b₃ * a₂ + k₁ * a₂ + (b₁ * b₂ + a₃ * b₄ + b₃ * a₄ + a₃ * b₄ + a₃ * k₂ + k₁ * b₂ + b₃ * k₂) := by ac_rfl
  rw [this, h]
  clear this h
  have h := congrArg (a₃ * ·) h₂
  simp [Semiring.left_distrib] at h
  have : b₁ * a₂ + a₃ * a₂ + k₁ * a₂ + (b₁ * b₂ + a₃ * b₄ + b₃ * a₄ + a₃ * b₄ + a₃ * k₂ + k₁ * b₂ + b₃ * k₂) =
         a₃ * a₂ + a₃ * b₄ + a₃ * k₂ + (b₁ * a₂ + k₁ * a₂ + b₁ * b₂ + b₃ * a₄ + a₃ * b₄ + k₁ * b₂ + b₃ * k₂) := by ac_rfl
  rw [this, h]
  clear this h
  have h := congrArg (· * b₂) h₁
  simp [Semiring.right_distrib] at h
  have : a₃ * b₂ + a₃ * a₄ + a₃ * k₂ + (b₁ * a₂ + k₁ * a₂ + b₁ * b₂ + b₃ * a₄ + a₃ * b₄ + k₁ * b₂ + b₃ * k₂) =
         b₁ * b₂ + a₃ * b₂ + k₁ * b₂ + (a₃ * a₄ + a₃ * k₂ + b₁ * a₂ + k₁ * a₂ + b₃ * a₄ + a₃ * b₄ + b₃ * k₂) := by ac_rfl
  rw [this, ← h]
  clear this h
  have h := congrArg (b₃ * ·) h₂
  simp [Semiring.left_distrib] at h
  have : a₁ * b₂ + b₃ * b₂ + k₁ * b₂ + (a₃ * a₄ + a₃ * k₂ + b₁ * a₂ + k₁ * a₂ + b₃ * a₄ + a₃ * b₄ + b₃ * k₂) =
         b₃ * b₂ + b₃ * a₄ + b₃ * k₂ + (a₁ * b₂ + k₁ * b₂ + a₃ * a₄ + a₃ * k₂ + b₁ * a₂ + k₁ * a₂ + a₃ * b₄) := by ac_rfl
  rw [this, ← h]
  clear this h
  ac_rfl

def Q.mk (p : α × α) : Q α :=
  Quot.mk (r α) p

def Q.liftOn₂ (q₁ q₂ : Q α)
    (f : α × α → α × α → β)
    (h : ∀ {a₁ b₁ a₂ b₂}, r α a₁ a₂ → r α b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    : β := by
  apply Quot.lift (fun (a₁ : α × α) => Quot.lift (f a₁)
    (fun (a b : α × α) => @h a₁ a a₁ b (r_rfl a₁)) q₂) _ q₁
  intros
  induction q₂ using Quot.ind
  apply h; assumption; apply r_rfl

attribute [local simp] Q.mk Q.liftOn₂

def Q.ind {β : Q α → Prop} (mk : ∀ (a : α × α), β (Q.mk a)) (q : Q α) : β q :=
  Quot.ind mk q

@[local simp] def natCast (n : Nat) : Q α :=
  Q.mk (n, 0)

@[local simp] def intCast (n : Int) : Q α :=
  if n < 0 then Q.mk (0, n.natAbs) else Q.mk (n.natAbs, 0)

@[local simp] def sub (q₁ q₂ : Q α) : Q α :=
  Q.liftOn₂ q₁ q₂ (fun (a, b) (c, d) => Q.mk (a + d, c + b))
    (by intro (a₁, b₁) (a₂, b₂) (a₃, b₃) (a₄, b₄)
        simp; intro k₁ h₁ k₂ h₂; apply Quot.sound; simp
        refine ⟨k₁ + k₂, ?_⟩
        have : a₁ + b₂ + (a₄ + b₃) + (k₁ + k₂) = a₁ + b₃ + k₁ + (b₂ + a₄ + k₂) := by ac_rfl
        rw [this, h₁, ← h₂]
        ac_rfl)

@[local simp] def add (q₁ q₂ : Q α) : Q α :=
  Q.liftOn₂ q₁ q₂ (fun (a, b) (c, d) => Q.mk (a + c, b + d))
    (by intro (a₁, b₁) (a₂, b₂) (a₃, b₃) (a₄, b₄)
        simp; intro k₁ h₁ k₂ h₂; apply Quot.sound; simp
        refine ⟨k₁ + k₂, ?_⟩
        have : a₁ + a₂ + (b₃ + b₄) + (k₁ + k₂) = a₁ + b₃ + k₁ + (a₂ + b₄ + k₂) := by ac_rfl
        rw [this, h₁, h₂]
        ac_rfl)

@[local simp] def mul (q₁ q₂ : Q α) : Q α :=
  Q.liftOn₂ q₁ q₂ (fun (a, b) (c, d) => Q.mk (a*c + b*d, a*d + b*c))
    (by intro (a₁, b₁) (a₂, b₂) (a₃, b₃) (a₄, b₄)
        simp; intro k₁ h₁ k₂ h₂; apply Quot.sound; simp
        apply mul_helper h₁ h₂)

@[local simp] def neg (q : Q α) : Q α :=
  q.liftOn (fun (a, b) => Q.mk (b, a))
    (by intro (a₁, b₁) (a₂, b₂)
        simp; intro k h; apply Quot.sound; simp
        exact ⟨k, h.symm⟩)

attribute [local simp]
  Quot.liftOn Semiring.add_zero AddCommMonoid.zero_add Semiring.mul_one Semiring.one_mul
  Semiring.natCast_zero Semiring.natCast_one Semiring.mul_zero Semiring.zero_mul

theorem neg_add_cancel (a : Q α) : add (neg a) a = natCast 0 := by
  obtain ⟨⟨_, _⟩⟩ := a
  simp
  apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem add_comm (a b : Q α) : add a b = add b a := by
  obtain ⟨⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩⟩ := b
  simp; apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem add_zero (a : Q α) : add a (natCast 0) = a := by
  induction a using Quot.ind
  next a => cases a; simp

theorem add_assoc (a b c : Q α) : add (add a b) c = add a (add b c) := by
  obtain ⟨⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩⟩ := b
  obtain ⟨⟨_, _⟩⟩ := c
  simp; apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem sub_eq_add_neg (a b : Q α) : sub a b = add a (neg b) := by
  obtain ⟨⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩⟩ := b
  simp; apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem intCast_neg (i : Int) : intCast (α := α) (-i) = neg (intCast i) := by
  simp; split <;> split <;> simp
  next => omega
  next =>
    apply Quot.sound; simp; refine ⟨0, ?_⟩; simp at *
    have : i = 0 := by apply Int.le_antisymm <;> assumption
    simp [this]

theorem intCast_ofNat (n : Nat) : intCast (α := α) (OfNat.ofNat (α := Int) n) = natCast n := by
  rfl

theorem ofNat_succ (a : Nat) : natCast (α := α) (a + 1) = add (natCast a) (natCast 1) := by
  simp; apply Quot.sound; simp [Semiring.natCast_add]

theorem mul_assoc (a b c : Q α) : mul (mul a b) c = mul a (mul b c) := by
  obtain ⟨⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩⟩ := b
  obtain ⟨⟨_, _⟩⟩ := c
  simp; apply Quot.sound
  simp [Semiring.left_distrib, Semiring.right_distrib]; refine ⟨0, ?_⟩; ac_rfl

theorem mul_one (a : Q α) : mul a (natCast 1) = a := by
obtain ⟨⟨_, _⟩⟩ := a; simp

theorem one_mul (a : Q α) : mul (natCast 1) a = a := by
  obtain ⟨⟨_, _⟩⟩ := a; simp

theorem zero_mul (a : Q α) : mul (natCast 0) a = natCast 0 := by
  obtain ⟨⟨_, _⟩⟩ := a; simp

theorem mul_zero (a : Q α) : mul a (natCast 0) = natCast 0 := by
  obtain ⟨⟨_, _⟩⟩ := a; simp

theorem left_distrib (a b c : Q α) : mul a (add b c) = add (mul a b) (mul a c) := by
  obtain ⟨⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩⟩ := b
  obtain ⟨⟨_, _⟩⟩ := c
  simp; apply Quot.sound
  simp [Semiring.left_distrib]; refine ⟨0, ?_⟩; ac_rfl

theorem right_distrib (a b c : Q α) : mul (add a b) c = add (mul a c) (mul b c) := by
  obtain ⟨⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩⟩ := b
  obtain ⟨⟨_, _⟩⟩ := c
  simp; apply Quot.sound
  simp [Semiring.right_distrib]; refine ⟨0, ?_⟩; ac_rfl

def npow (a : Q α) (n : Nat)  : Q α :=
  match n with
  | 0 => natCast 1
  | n+1 => mul (npow a n) a

theorem pow_zero (a : Q α) : npow a 0 = natCast 1 := rfl

theorem pow_succ (a : Q α) (n : Nat) : npow a (n+1) = mul (npow a n) a := rfl

def nsmul (n : Nat) (a : Q α) : Q α :=
  mul (natCast n) a

def zsmul (i : Int) (a : Q α) : Q α :=
  mul (intCast i) a

theorem neg_zsmul (i : Int) (a : Q α) : zsmul (-i) a = neg (zsmul i a) := by
  obtain ⟨⟨_, _⟩⟩ := a
  simp [zsmul]
  split <;> rename_i h₁
  · split <;> rename_i h₂
    · omega
    · simp
  · split <;> rename_i h₂
    · simp
    · have : i = 0 := by omega
      simp [this]

def ofSemiring : Ring (Q α) := {
  nsmul := ⟨nsmul⟩
  zsmul := ⟨zsmul⟩
  ofNat   := fun n => ⟨natCast n⟩
  natCast := ⟨natCast⟩
  intCast := ⟨intCast⟩
  npow := ⟨npow⟩
  add, sub, mul, neg,
  add_comm, add_assoc, add_zero
  neg_add_cancel, sub_eq_add_neg
  mul_one, one_mul, zero_mul, mul_zero, mul_assoc,
  left_distrib, right_distrib, pow_zero, pow_succ,
  intCast_neg, ofNat_succ, neg_zsmul
}

attribute [instance] ofSemiring

@[local simp] private theorem mk_add_mk {a₁ a₂ b₁ b₂ : α} :
    Q.mk (a₁, a₂) + Q.mk (b₁, b₂) = Q.mk (a₁ + b₁, a₂ + b₂) := by
  rfl

@[local simp] private theorem mk_mul_mk {a₁ a₂ b₁ b₂ : α} :
    Q.mk (a₁, a₂) * Q.mk (b₁, b₂) = Q.mk (a₁*b₁ + a₂*b₂, a₁*b₂ + a₂*b₁) := by
  rfl

@[local simp] def toQ (a : α) : Q α :=
  Q.mk (a, 0)

attribute [-simp] Q.mk

/-! Embedding theorems -/

theorem toQ_add (a b : α) : toQ (a + b) = toQ a + toQ b := by
  simp

theorem toQ_mul (a b : α) : toQ (a * b) = toQ a * toQ b := by
  simp

theorem toQ_natCast (n : Nat) : toQ (natCast (α := α) n) = natCast n := by
  simp; apply Quot.sound; simp; refine ⟨0, ?_⟩; rfl

theorem toQ_ofNat (n : Nat) : toQ (OfNat.ofNat (α := α) n) = OfNat.ofNat (α := Q α) n := by
  simp; apply Quot.sound; rw [Semiring.ofNat_eq_natCast]; simp

theorem toQ_pow (a : α) (n : Nat) : toQ (a ^ n) = toQ a ^ n := by
  induction n
  next => simp; apply Quot.sound; simp [Semiring.pow_zero]
  next n ih => simp [-toQ, Semiring.pow_succ, toQ_mul, ih]

/-!
Helper definitions and theorems for proving `toQ` is injective when
`CommSemiring` has the right_cancel property
-/

private def rel (h : Equivalence (r α)) (q₁ q₂ : Q α) : Prop :=
  Q.liftOn₂ q₁ q₂
    (fun a₁ a₂ => r α a₁ a₂)
    (by intro a₁ b₁ a₂ b₂ h₁ h₂
        simp [-r]; constructor
        next => intro h₃; exact h.trans (h.symm h₁) (h.trans h₃ h₂)
        next => intro h₃; exact h.trans h₁ (h.trans h₃ (h.symm h₂)))

private theorem rel_rfl (h : Equivalence (r α)) (q : Q α) : rel h q q := by
  induction q using Quot.ind
  simp [rel, Semiring.add_comm]

private theorem helper (h : Equivalence (r α)) (q₁ q₂ : Q α) : q₁ = q₂ → rel h q₁ q₂ := by
  intro h; subst q₁; apply rel_rfl h

theorem Q.exact : Q.mk a = Q.mk b → r α a b := by
  apply helper
  constructor; exact r_rfl; exact r_sym; exact r_trans

-- If the CommSemiring has the `AddRightCancel` property then `toQ` is injective
theorem toQ_inj [AddRightCancel α] {a b : α} : toQ a = toQ b → a = b := by
  simp; intro h₁
  replace h₁ := Q.exact h₁
  simp at h₁
  obtain ⟨k, h₁⟩ := h₁
  exact AddRightCancel.add_right_cancel a b k h₁

instance [Semiring α] [AddRightCancel α] [NoNatZeroDivisors α] : NoNatZeroDivisors (OfSemiring.Q α) where
  no_nat_zero_divisors := by
    intro k a b h₁ h₂
    replace h₂ : mul (natCast k) a = mul (natCast k) b := h₂
    obtain ⟨⟨a₁, a₂⟩⟩ := a
    obtain ⟨⟨b₁, b₂⟩⟩ := b
    simp [mul] at h₂
    replace h₂ := Q.exact h₂
    simp [r] at h₂
    rcases h₂ with ⟨k', h₂⟩
    replace h₂ := AddRightCancel.add_right_cancel _ _ _ h₂
    simp only [← Semiring.left_distrib] at h₂
    simp only [← Semiring.nsmul_eq_natCast_mul] at h₂
    replace h₂ := NoNatZeroDivisors.no_nat_zero_divisors k (a₁ + b₂) (a₂ + b₁) h₁ h₂
    apply Quot.sound; simp [r]; exists 0; simp [h₂]

instance {p} [Semiring α] [AddRightCancel α] [IsCharP α p] : IsCharP (OfSemiring.Q α) p where
  ofNat_ext_iff := by
    intro x y
    constructor
    next =>
      intro h
      replace h : natCast x = natCast y := h; simp at h
      replace h := Q.exact h; simp [r] at h
      rcases h with ⟨k, h⟩
      replace h : OfNat.ofNat (α := α) x = OfNat.ofNat y := by
        replace h := AddRightCancel.add_right_cancel _ _ _ h
        simp [Semiring.ofNat_eq_natCast, h]
      have := IsCharP.ofNat_ext_iff p |>.mp h
      simp at this; assumption
    next =>
      intro h
      have := IsCharP.ofNat_ext_iff (α := α) p |>.mpr h
      apply Quot.sound
      exists 0; simp [← Semiring.ofNat_eq_natCast, this]

instance [LE α] [IsPreorder α] [OrderedAdd α] : LE (OfSemiring.Q α) where
  le a b := Q.liftOn₂ a b (fun (a, b) (c, d) => a + d ≤ b + c)
    (by intro (a₁, b₁) (a₂, b₂) (a₃, b₃) (a₄, b₄)
        simp; intro k₁ h₁ k₂ h₂
        rw [OrderedAdd.add_le_left_iff (b₃ + k₁)]
        have : a₁ + b₂ + (b₃ + k₁) = a₁ + b₃ + k₁ + b₂ := by ac_rfl
        rw [this, h₁]; clear this
        rw [OrderedAdd.add_le_left_iff (a₄ + k₂)]
        have : b₁ + a₃ + k₁ + b₂ + (a₄ + k₂) = b₂ + a₄ + k₂ + b₁ + a₃ + k₁ := by ac_rfl
        rw [this, ← h₂]; clear this
        have : a₂ + b₄ + k₂ + b₁ + a₃ + k₁ = a₃ + b₄ + (a₂ + b₁ + k₁ + k₂) := by ac_rfl
        rw [this]; clear this
        have : b₁ + a₂ + (b₃ + k₁) + (a₄ + k₂) = b₃ + a₄ + (a₂ + b₁ + k₁ + k₂) := by ac_rfl
        rw [this]; clear this
        rw [← OrderedAdd.add_le_left_iff])

instance [LE α] [IsPreorder α] [OrderedAdd α] : LT (OfSemiring.Q α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

@[local simp] theorem mk_le_mk [LE α] [IsPreorder α] [OrderedAdd α] {a₁ a₂ b₁ b₂ : α}  :
    Q.mk (a₁, a₂) ≤ Q.mk (b₁, b₂) ↔ a₁ + b₂ ≤ a₂ + b₁ := by
  rfl

instance [LE α] [IsPreorder α] [OrderedAdd α] : IsPreorder (OfSemiring.Q α) where
  le_refl a := by
    obtain ⟨⟨a₁, a₂⟩⟩ := a
    change Q.mk _ ≤ Q.mk _
    simp only [mk_le_mk]
    simp [Semiring.add_comm]; exact le_refl (a₁ + a₂)
  le_trans {a b c} h₁ h₂ := by
    induction a using Q.ind with | _ a
    induction b using Q.ind with | _ b
    induction c using Q.ind with | _ c
    rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩; rcases c with ⟨c₁, c₂⟩
    simp only [mk_le_mk] at h₁ h₂ ⊢
    rw [OrderedAdd.add_le_left_iff (b₁ + b₂)]
    have : a₁ + c₂ + (b₁ + b₂) = a₁ + b₂ + (b₁ + c₂) := by ac_rfl
    rw [this]; clear this
    have : a₂ + c₁ + (b₁ + b₂) = a₂ + b₁ + (b₂ + c₁) := by ac_rfl
    rw [this]; clear this
    exact OrderedAdd.add_le_add h₁ h₂

@[local simp] private theorem mk_lt_mk [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a₁ a₂ b₁ b₂ : α}  :
    Q.mk (a₁, a₂) < Q.mk (b₁, b₂) ↔ a₁ + b₂ < a₂ + b₁ := by
  simp [lt_iff_le_and_not_ge, Semiring.add_comm]

@[local simp] private theorem mk_pos [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a₁ a₂ : α} :
    0 < Q.mk (a₁, a₂) ↔ a₂ < a₁ := by
  simp [← toQ_ofNat, toQ, mk_lt_mk, AddCommMonoid.zero_add]

@[local simp]
theorem toQ_le [LE α] [IsPreorder α] [OrderedAdd α] {a b : α} : toQ a ≤ toQ b ↔ a ≤ b := by
  simp

@[local simp]
theorem toQ_lt [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a b : α} : toQ a < toQ b ↔ a < b := by
  simp [lt_iff_le_and_not_ge]

instance [LE α] [IsPreorder α] [OrderedAdd α] : OrderedAdd (OfSemiring.Q α) where
  add_le_left_iff := by
    intro a b c
    obtain ⟨⟨a₁, a₂⟩⟩ := a
    obtain ⟨⟨b₁, b₂⟩⟩ := b
    obtain ⟨⟨c₁, c₂⟩⟩ := c
    change a₁ + b₂ ≤ a₂ + b₁ ↔ (a₁ + c₁) + _ ≤ _
    have : a₁ + c₁ + (b₂ + c₂) = a₁ + b₂ + (c₁ + c₂) := by ac_rfl
    rw [this]; clear this
    have : a₂ + c₂ + (b₁ + c₁) = a₂ + b₁ + (c₁ + c₂) := by ac_rfl
    rw [this]; clear this
    rw [← OrderedAdd.add_le_left_iff]

-- This perhaps works in more generality than `ExistsAddOfLT`?
instance [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] [ExistsAddOfLT α] : OrderedRing (OfSemiring.Q α) where
  zero_lt_one := by
    rw [← toQ_ofNat, ← toQ_ofNat, toQ_lt]
    exact OrderedRing.zero_lt_one
  mul_lt_mul_of_pos_left := by
    intro a b c h₁ h₂
    induction a using Q.ind with | _ a
    induction b using Q.ind with | _ b
    induction c using Q.ind with | _ c
    rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩; rcases c with ⟨c₁, c₂⟩
    simp at h₁ h₂ ⊢
    obtain ⟨d, d_pos, rfl⟩ := ExistsAddOfLT.exists_add_of_le h₂
    simp [Semiring.right_distrib]
    have : c₂ * a₁ + d * a₁ + c₂ * a₂ + (c₂ * b₂ + d * b₂ + c₂ * b₁) =
      c₂ * a₁ + c₂ * a₂ + c₂ * b₁ + c₂ * b₂ + (d * a₁ + d * b₂) := by ac_rfl
    rw [this]; clear this
    have : c₂ * a₂ + d * a₂ + c₂ * a₁ + (c₂ * b₁ + d * b₁ + c₂ * b₂) =
      c₂ * a₁ + c₂ * a₂ + c₂ * b₁ + c₂ * b₂ + (d * a₂ + d * b₁) := by ac_rfl
    rw [this]; clear this
    rw [← OrderedAdd.add_lt_right_iff]
    simpa [Semiring.left_distrib] using OrderedRing.mul_lt_mul_of_pos_left h₁ d_pos
  mul_lt_mul_of_pos_right := by
    intro a b c h₁ h₂
    induction a using Q.ind with | _ a
    induction b using Q.ind with | _ b
    induction c using Q.ind with | _ c
    rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩; rcases c with ⟨c₁, c₂⟩
    simp at h₁ h₂ ⊢
    obtain ⟨d, d_pos, rfl⟩ := ExistsAddOfLT.exists_add_of_le h₂
    simp [Semiring.left_distrib]
    have : a₁ * c₂ + a₁ * d + a₂ * c₂ + (b₁ * c₂ + (b₂ * c₂ + b₂ * d)) =
      a₁ * c₂ + a₂ * c₂ + b₁ * c₂ + b₂ * c₂ + (a₁ * d + b₂ * d) := by ac_rfl
    rw [this]; clear this
    have : a₁ * c₂ + (a₂ * c₂ + a₂ * d) + (b₁ * c₂ + b₁ * d + b₂ * c₂) =
      a₁ * c₂ + a₂ * c₂ + b₁ * c₂ + b₂ * c₂ + (a₂ * d + b₁ * d) := by ac_rfl
    rw [this]; clear this
    rw [← OrderedAdd.add_lt_right_iff]
    simpa [Semiring.right_distrib] using OrderedRing.mul_lt_mul_of_pos_right h₁ d_pos

end OfSemiring
end Lean.Grind.Ring

open Lean.Grind.Ring

namespace Lean.Grind.CommRing

namespace OfCommSemiring

variable (α : Type u) [CommSemiring α]

local instance : Std.Associative (· + · : α → α → α) where
  assoc := Semiring.add_assoc
local instance : Std.Commutative (· + · : α → α → α) where
  comm := Semiring.add_comm
local instance : Std.Associative (· * · : α → α → α) where
  assoc := Semiring.mul_assoc
local instance : Std.Commutative (· * · : α → α → α) where
  comm := CommSemiring.mul_comm

variable {α}

attribute [local simp] OfSemiring.Q.mk OfSemiring.Q.liftOn₂ Semiring.add_zero

theorem mul_comm (a b : OfSemiring.Q α) : OfSemiring.mul a b = OfSemiring.mul b a := by
  obtain ⟨⟨a₁, a₂⟩⟩ := a
  obtain ⟨⟨b₁, b₂⟩⟩ := b
  apply Quot.sound; refine ⟨0, ?_⟩; simp; ac_rfl

def ofCommSemiring : CommRing (OfSemiring.Q α) :=
  { OfSemiring.ofSemiring with
    mul_comm := mul_comm }

attribute [instance] ofCommSemiring

/-
Remark: `↑a` is notation for `OfSemiring.toQ a`.
We want to hide `OfSemiring.toQ` applications in the diagnostic information produced by
the `ring` procedure in `grind`.
-/
@[app_unexpander OfSemiring.toQ]
meta def toQUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $a:term) => `(↑$a)
  | _ => throw ()

end OfCommSemiring
end Lean.Grind.CommRing
