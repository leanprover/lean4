/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kim Morrison
-/
module

prelude
import Init.Grind.Ring.Basic
import all Init.Data.AC

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
  cases a; cases b; cases c;
  next a₁ a₂ b₁ b₂ c₁ c₂ =>
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
  Quot.liftOn Semiring.add_zero Semiring.zero_add Semiring.mul_one Semiring.one_mul
  Semiring.natCast_zero Semiring.natCast_one Semiring.mul_zero Semiring.zero_mul

theorem neg_add_cancel (a : Q α) : add (neg a) a = natCast 0 := by
  induction a using Quot.ind
  next a =>
  cases a; simp
  apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem add_comm (a b : Q α) : add a b = add b a := by
  induction a using Quot.ind
  induction b using Quot.ind
  next a b =>
  cases a; cases b; simp; apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem add_zero (a : Q α) : add a (natCast 0) = a := by
  induction a using Quot.ind
  next a => cases a; simp

theorem add_assoc (a b c : Q α) : add (add a b) c = add a (add b c) := by
  induction a using Quot.ind
  induction b using Quot.ind
  induction c using Quot.ind
  next a b c =>
  cases a; cases b; cases c; simp; apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem sub_eq_add_neg (a b : Q α) : sub a b = add a (neg b) := by
  induction a using Quot.ind
  induction b using Quot.ind
  next a b =>
  cases a; cases b; simp; apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

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
  induction a using Quot.ind
  induction b using Quot.ind
  induction c using Quot.ind
  next a b c =>
  cases a; cases b; cases c; simp; apply Quot.sound
  simp [Semiring.left_distrib, Semiring.right_distrib]; refine ⟨0, ?_⟩; ac_rfl

theorem mul_one (a : Q α) : mul a (natCast 1) = a := by
  induction a using Quot.ind
  next a => cases a; simp

theorem one_mul (a : Q α) : mul (natCast 1) a = a := by
  induction a using Quot.ind
  next a => cases a; simp

theorem zero_mul (a : Q α) : mul (natCast 0) a = natCast 0 := by
  induction a using Quot.ind
  next a => cases a; simp

theorem mul_zero (a : Q α) : mul a (natCast 0) = natCast 0 := by
  induction a using Quot.ind
  next a => cases a; simp

theorem left_distrib (a b c : Q α) : mul a (add b c) = add (mul a b) (mul a c) := by
  induction a using Quot.ind
  induction b using Quot.ind
  induction c using Quot.ind
  next a b c =>
  cases a; cases b; cases c; simp; apply Quot.sound
  simp [Semiring.left_distrib, Semiring.right_distrib]; refine ⟨0, ?_⟩; ac_rfl

theorem right_distrib (a b c : Q α) : mul (add a b) c = add (mul a c) (mul b c) := by
  induction a using Quot.ind
  induction b using Quot.ind
  induction c using Quot.ind
  next a b c =>
  cases a; cases b; cases c; simp; apply Quot.sound
  simp [Semiring.left_distrib, Semiring.right_distrib]; refine ⟨0, ?_⟩; ac_rfl

def hPow (a : Q α) (n : Nat)  : Q α :=
  match n with
  | 0 => natCast 1
  | n+1 => mul (hPow a n) a

private theorem pow_zero (a : Q α) : hPow a 0 = natCast 1 := rfl

private theorem pow_succ (a : Q α) (n : Nat) : hPow a (n+1) = mul (hPow a n) a := rfl

def ofSemiring : Ring (Q α) := {
  ofNat   := fun n => ⟨natCast n⟩
  natCast := ⟨natCast⟩
  intCast := ⟨intCast⟩
  add, sub, mul, neg, hPow
  add_comm, add_assoc, add_zero
  neg_add_cancel, sub_eq_add_neg
  mul_one, one_mul, zero_mul, mul_zero, mul_assoc,
  left_distrib, right_distrib, pow_zero, pow_succ,
  intCast_neg, ofNat_succ
}

attribute [local instance] ofSemiring

@[local simp] def toQ (a : α) : Q α :=
  Q.mk (a, 0)

/-! Embedding theorems -/

theorem toQ_add (a b : α) : toQ (a + b) = toQ a + toQ b := by
  simp; apply Quot.sound; simp

theorem toQ_mul (a b : α) : toQ (a * b) = toQ a * toQ b := by
  simp; apply Quot.sound; simp

theorem toQ_natCast (n : Nat) : toQ (natCast (α := α) n) = natCast n := by
  simp; apply Quot.sound; simp [natCast]; refine ⟨0, ?_⟩; rfl

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
  induction a using Quot.ind
  induction b using Quot.ind
  next a b =>
  cases a; cases b; apply Quot.sound; refine ⟨0, ?_⟩; simp; ac_rfl

def ofCommSemiring : CommRing (OfSemiring.Q α) :=
  { OfSemiring.ofSemiring with
    mul_comm := mul_comm }

end OfCommSemiring

end Lean.Grind.CommRing
