/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ordered.Module
public import Init.Data.AC
import all Init.Data.AC

public section

namespace Lean.Grind.IntModule

namespace OfNatModule
variable (α : Type u)
variable [NatModule α]

-- Helper instance for `ac_rfl`
local instance : Std.Associative (· + · : α → α → α) where
  assoc := AddCommMonoid.add_assoc
local instance : Std.Commutative (· + · : α → α → α) where
  comm := AddCommMonoid.add_comm

@[local simp] private theorem exists_true : ∃ (_ : α), True := ⟨0, trivial⟩

@[local simp] def r : (α × α) → (α × α) → Prop
  | (a, b), (c, d) => ∃ k, a + d + k = b + c + k

def Q := Quot (r α)

variable {α}

theorem r_rfl (a : α × α) : r α a a := by
  cases a; refine ⟨0, ?_⟩; simp [AddCommMonoid.add_zero]; ac_rfl

theorem r_sym {a b : α × α} : r α a b → r α b a := by
  cases a; cases b; simp [r]; intro h w; refine ⟨h, ?_⟩; simp [w, AddCommMonoid.add_comm]

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

attribute [local simp] Q.mk Q.liftOn₂ AddCommMonoid.add_zero

def Q.ind {β : Q α → Prop} (mk : ∀ (a : α × α), β (Q.mk a)) (q : Q α) : β q :=
  Quot.ind mk q

@[local simp] def nsmul (n : Nat) (q : Q α) : (Q α) :=
  q.liftOn (fun (a, b) => Q.mk (n • a, n • b))
    (by intro (a₁, b₁) (a₂, b₂)
        simp; intro k h; apply Quot.sound; simp
        refine ⟨n • k, ?_⟩
        replace h := congrArg (fun x : α => n • x) h
        simpa [NatModule.nsmul_add] using h)

@[local simp] def zsmul (n : Int) (q : Q α) : (Q α) :=
  q.liftOn (fun (a, b) => if n < 0 then Q.mk (n.natAbs • b, n.natAbs • a) else Q.mk (n.natAbs • a, n.natAbs • b))
    (by intro (a₁, b₁) (a₂, b₂)
        simp; intro k h;
        split
        · apply Quot.sound; simp
          refine ⟨n.natAbs • k, ?_⟩
          replace h := congrArg (fun x : α => n.natAbs • x) h
          simpa [NatModule.nsmul_add] using h.symm
        · apply Quot.sound; simp
          refine ⟨n.natAbs • k, ?_⟩
          replace h := congrArg (fun x : α => n.natAbs • x) h
          simpa [NatModule.nsmul_add] using h)

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

@[local simp] def neg (q : Q α) : Q α :=
  q.liftOn (fun (a, b) => Q.mk (b, a))
    (by intro (a₁, b₁) (a₂, b₂)
        simp; intro k h; apply Quot.sound; simp
        exact ⟨k, h.symm⟩)

attribute [local simp]
  Quot.liftOn AddCommMonoid.add_zero AddCommMonoid.zero_add NatModule.one_nsmul NatModule.zero_nsmul NatModule.nsmul_zero
  NatModule.nsmul_add NatModule.add_nsmul

@[local simp] def zero : Q α :=
  Q.mk (0, 0)

theorem neg_add_cancel (a : Q α) : add (neg a) a = zero := by
  obtain ⟨⟨_, _⟩⟩ := a
  simp
  apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem add_comm (a b : Q α) : add a b = add b a := by
  obtain ⟨⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩⟩ := b
  simp; apply Quot.sound; simp; refine ⟨0, ?_⟩; ac_rfl

theorem add_zero (a : Q α) : add a zero = a := by
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

theorem one_zsmul (a : Q α) : zsmul 1 a = a := by
  induction a using Quot.ind
  next a => cases a; simp

theorem zero_zsmul (a : Q α) : zsmul 0 a = zero := by
  induction a using Quot.ind
  next a => cases a; simp

theorem add_zsmul (a b : Int) (c : Q α) : zsmul (a + b) c = add (zsmul a c) (zsmul b c) := by
  induction c using Q.ind with | _ c
  rcases c with ⟨c₁, c₂⟩; simp
  by_cases hb : b < 0
  · simp only [if_pos hb]
    by_cases ha : a < 0
    · simp only [if_pos ha]
      rw [if_pos (by omega)]
      apply Quot.sound
      refine ⟨0, ?_⟩
      rw [Int.natAbs_add_of_nonpos (by omega) (by omega), NatModule.add_nsmul, NatModule.add_nsmul]
      ac_rfl
    · split
      · apply Quot.sound
        refine ⟨a.natAbs • c₁ + a.natAbs • c₂, ?_⟩
        have : (a + b).natAbs + a.natAbs = b.natAbs := by omega
        simp [← this]
        ac_rfl
      · apply Quot.sound
        refine ⟨b.natAbs • c₁ + b.natAbs • c₂, ?_⟩
        have : (a + b).natAbs + b.natAbs = a.natAbs := by omega
        simp [← this]
        ac_rfl
  · simp only [if_neg hb]
    by_cases ha : a < 0
    · split
      · apply Quot.sound
        refine ⟨a.natAbs • c₁ + a.natAbs • c₂, ?_⟩
        have : (a + b).natAbs + b.natAbs = a.natAbs := by omega
        simp [← this]
        ac_rfl
      · apply Quot.sound
        refine ⟨b.natAbs • c₁ + b.natAbs • c₂, ?_⟩
        have : (a + b).natAbs + a.natAbs = b.natAbs := by omega
        simp [← this]
        ac_rfl
    · simp only [if_neg ha]
      rw [if_neg (by omega)]
      apply Quot.sound
      refine ⟨0, ?_⟩
      rw [Int.natAbs_add_of_nonneg (by omega) (by omega), NatModule.add_nsmul, NatModule.add_nsmul]
      ac_rfl

theorem zsmul_natCast_eq_nsmul (n : Nat) (a : Q α) : zsmul (n : Int) a = nsmul n a := by
  induction a using Q.ind with | _ a
  rcases a with ⟨a₁, a₂⟩; simp; omega

def ofNatModule : IntModule (Q α) := {
  nsmul := ⟨nsmul⟩,
  zsmul := ⟨zsmul⟩,
  zero,
  add, sub, neg,
  add_comm, add_assoc, add_zero,
  neg_add_cancel, sub_eq_add_neg,
  one_zsmul, zero_zsmul, add_zsmul,
  zsmul_natCast_eq_nsmul
}

attribute [instance] ofNatModule

@[local simp] def toQ (a : α) : Q α :=
  Q.mk (a, 0)

/-! Embedding theorems -/

theorem toQ_add (a b : α) : toQ (a + b) = toQ a + toQ b := by
  simp; apply Quot.sound; simp

theorem toQ_zero : toQ (0 : α) = 0 := by
  simp; apply Quot.sound; simp

theorem toQ_smul (n : Nat) (a : α) : toQ (n • a) = (↑n : Int) • toQ a := by
  simp; apply Quot.sound; simp

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
  simp [rel, AddCommMonoid.add_comm]

private theorem helper (h : Equivalence (r α)) (q₁ q₂ : Q α) : q₁ = q₂ → rel h q₁ q₂ := by
  intro h; subst q₁; apply rel_rfl h

theorem Q.exact : Q.mk a = Q.mk b → r α a b := by
  apply helper
  constructor; exact r_rfl; exact r_sym; exact r_trans

-- If the `NatModule` has the `AddRightCancel` property then `toQ` is injective
theorem toQ_inj [AddRightCancel α] {a b : α} : toQ a = toQ b → a = b := by
  simp; intro h₁
  replace h₁ := Q.exact h₁
  simp at h₁
  obtain ⟨k, h₁⟩ := h₁
  exact AddRightCancel.add_right_cancel a b k h₁

instance [NatModule α] [AddRightCancel α] [NoNatZeroDivisors α] : NoNatZeroDivisors (OfNatModule.Q α) where
  no_nat_zero_divisors := by
    intro k a b h₁ h₂
    replace h₂ : k • a = k • b := h₂
    obtain ⟨⟨a₁, a₂⟩⟩ := a
    obtain ⟨⟨b₁, b₂⟩⟩ := b
    replace h₂ := Q.exact h₂
    simp [r] at h₂
    rcases h₂ with ⟨k', h₂⟩
    replace h₂ := AddRightCancel.add_right_cancel _ _ _ h₂
    simp [← NatModule.nsmul_add] at h₂
    replace h₂ := NoNatZeroDivisors.no_nat_zero_divisors k (a₁ + b₂) (a₂ + b₁) h₁ h₂
    apply Quot.sound; simp [r]; exists 0; simp [h₂]

instance [LE α] [LT α] [Preorder α] [OrderedAdd α] : LE (OfNatModule.Q α) where
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

instance [LE α] [LT α] [Preorder α] [OrderedAdd α] : LT (OfNatModule.Q α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

@[local simp] theorem mk_le_mk [LE α] [LT α] [Preorder α] [OrderedAdd α] {a₁ a₂ b₁ b₂ : α}  :
    Q.mk (a₁, a₂) ≤ Q.mk (b₁, b₂) ↔ a₁ + b₂ ≤ a₂ + b₁ := by
  rfl

instance [LE α] [LT α] [Preorder α] [OrderedAdd α] : Preorder (OfNatModule.Q α) where
  le_refl a := by
    obtain ⟨⟨a₁, a₂⟩⟩ := a
    change Q.mk _ ≤ Q.mk _
    simp only [mk_le_mk]
    simp [AddCommMonoid.add_comm]; exact Preorder.le_refl (a₁ + a₂)
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

attribute [-simp] Q.mk

@[local simp] private theorem mk_lt_mk [LE α] [LT α] [Preorder α] [OrderedAdd α] {a₁ a₂ b₁ b₂ : α}  :
    Q.mk (a₁, a₂) < Q.mk (b₁, b₂) ↔ a₁ + b₂ < a₂ + b₁ := by
  simp [Preorder.lt_iff_le_not_le, AddCommMonoid.add_comm]

@[local simp] private theorem mk_pos [LE α] [LT α] [Preorder α] [OrderedAdd α] {a₁ a₂ : α} :
    0 < Q.mk (a₁, a₂) ↔ a₂ < a₁ := by
  change Q.mk (0,0) < _ ↔ _
  simp [mk_lt_mk, AddCommMonoid.zero_add]

@[local simp]
theorem toQ_le [LE α] [LT α] [Preorder α] [OrderedAdd α] {a b : α} : toQ a ≤ toQ b ↔ a ≤ b := by
  simp

@[local simp]
theorem toQ_lt [LE α] [LT α] [Preorder α] [OrderedAdd α] {a b : α} : toQ a < toQ b ↔ a < b := by
  simp [Preorder.lt_iff_le_not_le]

instance [LE α] [LT α] [Preorder α] [OrderedAdd α] : OrderedAdd (OfNatModule.Q α) where
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

end OfNatModule
end Lean.Grind.IntModule
