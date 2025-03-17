/-!
# Testing for timeouts in typeclass synthesis

Example from Mathlib

Implemented in PR #2478 for issue #2451.
-/

set_option autoImplicit true

noncomputable section
section Mathlib.Logic.Relator

namespace Relator

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variable (R : α → β → Prop) (S : γ → δ → Prop)

def LiftFun (f : α → γ) (g : β → δ) : Prop :=
  ∀⦃a b⦄, R a b → S (f a) (g b)

infixr:40 " ⇒ " => LiftFun

end Relator

end Mathlib.Logic.Relator

section Mathlib.Data.Quot

namespace Quot

variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort _}

@[inherit_doc]
local notation:arg "⟦" a "⟧" => Quot.mk _ a

@[elab_as_elim]
protected theorem induction_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  ind h q

protected def map (f : α → β) (h : (ra ⇒ rb) f f) : Quot ra → Quot rb :=
  (Quot.lift fun x ↦ ⟦f x⟧) fun x y (h₁ : ra x y) ↦ Quot.sound <| h h₁

protected def lift₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun a ↦ Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha ↦ funext fun q ↦ Quot.induction_on q fun b ↦ hs a₁ a₂ b ha) q₁ q₂

protected def map₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) : Quot t :=
  Quot.lift₂ (fun a b ↦ Quot.mk t <| f a b) (fun a b₁ b₂ hb ↦ Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha ↦ Quot.sound (hs a₁ a₂ b ha)) q₁ q₂

end Quot

namespace Quotient

variable [sa : Setoid α] [sb : Setoid β]

variable {φ : Quotient sa → Quotient sb → Sort _}

notation:arg "⟦" a "⟧" => Quotient.mk _ a

variable {γ : Sort _} [sc : Setoid γ]

protected def map₂ (f : α → β → γ) (h : ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f) :
    Quotient sa → Quotient sb → Quotient sc :=
  Quotient.lift₂ (fun x y ↦ ⟦f x y⟧) fun _ _ _ _ h₁ h₂ ↦ Quot.sound <| h h₁ h₂

variable {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

protected def mk'' (a : α) : Quotient s₁ :=
  Quot.mk s₁.1 a

protected def map' (f : α → β) (h : (s₁.r ⇒ s₂.r) f f) : Quotient s₁ → Quotient s₂ :=
  Quot.map f h

protected def map₂' (f : α → β → γ) (h : (s₁.r ⇒ s₂.r ⇒ s₃.r) f f) :
    Quotient s₁ → Quotient s₂ → Quotient s₃ :=
  Quotient.map₂ f h

end Quotient


end Mathlib.Data.Quot

section Mathlib.Init.ZeroOne

class One (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

section Mathlib.Init.ZeroOne

section Mathlib.Logic.Function.Basic

namespace Function

variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α] [DecidableEq α']
  {f g : (a : α) → β a} {a : α} {b : β a}

def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

end Function

end Mathlib.Logic.Function.Basic

section Mathlib.Algebra.Group.Defs

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

class SMul (M : Type _) (α : Type _) where
  smul : M → α → α

infixr:73 " • " => HSMul.hSMul

instance instHSMul [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

class AddSemigroup (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm : ∀ a b : G, a * b = b * a

class AddCommSemigroup (G : Type u) extends AddSemigroup G where
  add_comm : ∀ a b : G, a + b = b + a

class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a

def npowRec [One M] [Mul M] : Nat → M → M
  | 0, _ => 1
  | n + 1, a => a * npowRec n a

def nsmulRec [Zero M] [Add M] : Nat → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmulRec n a

class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  nsmul : Nat → M → M := nsmulRec
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  nsmul_succ : ∀ (n : Nat) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZeroClass.toAdd

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : Nat → M → M := npowRec
  npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  npow_succ : ∀ (n : Nat) (x), npow (n + 1) x = x * npow n x := by intros; rfl

@[default_instance high] instance Monoid.Pow {M : Type _} [Monoid M] : Pow M Nat :=
  ⟨fun x n ↦ Monoid.npow n x⟩

instance AddMonoid.SMul {M : Type _} [AddMonoid M] : SMul Nat M :=
  ⟨AddMonoid.nsmul⟩

class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : Int → M → M
  | Int.ofNat n, a => npowRec n a
  | Int.negSucc n, a => (npowRec n.succ a)⁻¹

def zsmulRec {M : Type _} [Zero M] [Add M] [Neg M] : Int → M → M
  | Int.ofNat n, a => nsmulRec n a
  | Int.negSucc n, a => -nsmulRec n.succ a

section InvolutiveInv

class InvolutiveNeg (A : Type _) extends Neg A where
  neg_neg : ∀ x : A, - -x = x

class InvolutiveInv (G : Type _) extends Inv G where
  inv_inv : ∀ x : G, x⁻¹⁻¹ = x

end InvolutiveInv

def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  div := DivInvMonoid.div'
  div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  zpow : Int → G → G := zpowRec
  zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  zpow_succ' (n : Nat) (a : G) : zpow (Int.ofNat n.succ) a = a * zpow (Int.ofNat n) a := by
    intros; rfl
  zpow_neg' (n : Nat) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl

def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  sub := SubNegMonoid.sub'
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  zsmul : Int → G → G := zsmulRec
  zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  zsmul_succ' (n : Nat) (a : G) : zsmul (Int.ofNat n.succ) a = a + zsmul (Int.ofNat n) a := by
    intros; rfl
  zsmul_neg' (n : Nat) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by intros; rfl

instance SubNegMonoid.SMulInt {M} [SubNegMonoid M] : SMul Int M :=
  ⟨SubNegMonoid.zsmul⟩

class NegZeroClass (G : Type _) extends Zero G, Neg G where
  neg_zero : -(0 : G) = 0

class SubNegZeroMonoid (G : Type _) extends SubNegMonoid G, NegZeroClass G

class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  neg_add_rev (a b : G) : -(a + b) = -b + -a
  neg_eq_of_add (a b : G) : a + b = 0 → -a = b

class Group (G : Type u) extends DivInvMonoid G where
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg : ∀ a : A, -a + a = 0

instance (priority := 100) AddGroup.toSubtractionMonoid [AddGroup G] : SubtractionMonoid G :=
  { neg_neg := sorry
    neg_add_rev := sorry
    neg_eq_of_add := sorry }

class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

class CommGroup (G : Type u) extends Group G, CommMonoid G

end Mathlib.Algebra.Group.Defs

section Mathlib.Data.Pi.Algebra

variable {I : Type u} {f : I → Type v₁}

namespace Pi

instance instZero [∀ i, Zero <| f i] : Zero (∀ i : I, f i) :=
  ⟨fun _ => 0⟩

instance instAdd [∀ i, Add <| f i] : Add (∀ i : I, f i) :=
  ⟨fun f g i => f i + g i⟩

instance instSMul [∀ i, SMul α <| f i] : SMul α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

instance instNeg [∀ i, Neg <| f i] : Neg (∀ i : I, f i) :=
  ⟨fun f i => - (f i)⟩

instance instSub [∀ i, Sub <| f i] : Sub (∀ i : I, f i) :=
  ⟨fun f g i => f i - g i⟩

section

variable [DecidableEq I]

variable [∀ i, Zero (f i)]

def single (i : I) (x : f i) : ∀ (j : I), f j :=
  Function.update 0 i x

end

end Pi


end Mathlib.Data.Pi.Algebra

section Mathlib.Algebra.GroupWithZero.Defs

class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0

class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

class CommMonoidWithZero (M₀ : Type _) extends CommMonoid M₀, MonoidWithZero M₀

end Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Data.Nat.Cast.Defs

class AddMonoidWithOne (R : Type u) extends AddMonoid R, One R where

class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R

end Mathlib.Data.Nat.Cast.Defs

section Mathlib.Data.Int.Cast.Defs

class AddGroupWithOne (R : Type u) extends AddMonoidWithOne R, AddGroup R where

class AddCommGroupWithOne (R : Type u)
  extends AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R

end Mathlib.Data.Int.Cast.Defs

section Mathlib.Algebra.Group.Basic

variable [SubtractionMonoid α]

instance (priority := 100) SubtractionMonoid.toSubNegZeroMonoid : SubNegZeroMonoid α :=
  { SubtractionMonoid.toSubNegMonoid with
    neg_zero := sorry }

end Mathlib.Algebra.Group.Basic

section Mathlib.Algebra.Ring.Defs

class Distrib (R : Type _) extends Mul R, Add R where
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class LeftDistribClass (R : Type _) [Mul R] [Add R] : Prop where
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c

class RightDistribClass (R : Type _) [Mul R] [Add R] : Prop where
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance (priority := 100) Distrib.leftDistribClass (R : Type _) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩

instance (priority := 100) Distrib.rightDistribClass (R : Type _) [Distrib R] :
    RightDistribClass R :=
  ⟨Distrib.right_distrib⟩

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

class NonUnitalRing (α : Type _) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

class NonAssocRing (α : Type _) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α

class CommSemiring (R : Type u) extends Semiring R, CommMonoid R

instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }

instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] :
    CommMonoidWithZero α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }

section HasDistribNeg

class HasDistribNeg (α : Type _) [Mul α] extends InvolutiveNeg α where
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  mul_neg : ∀ x y : α, x * -y = -(x * y)

section Mul

variable [Mul α] [HasDistribNeg α]

end Mul

section MulZeroClass

variable [MulZeroClass α] [HasDistribNeg α]

instance (priority := 100) MulZeroClass.negZeroClass : NegZeroClass α :=
  { inferInstanceAs (Zero α), inferInstanceAs (InvolutiveNeg α) with
    neg_zero := sorry }

end MulZeroClass

end HasDistribNeg

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg := Neg.neg
  neg_neg := sorry
  neg_mul a b := sorry
  mul_neg a b := sorry

end NonUnitalNonAssocRing

section Ring

variable [Ring α] {a b c d e : α}

instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α :=
  { ‹Ring α› with
  zero_mul := sorry
  mul_zero := sorry }

instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α :=
  { ‹Ring α› with
  zero_mul := sorry
  mul_zero := sorry }

instance (priority := 200) : Semiring α :=
  { ‹Ring α› with }

end Ring

class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, CommSemigroup α

class CommRing (α : Type u) extends Ring α, CommMonoid α

instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }

end Mathlib.Algebra.Ring.Defs

section Mathlib.Data.FunLike.Basic

class FunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  coe : F → ∀ a : α, β a

variable (F α : Sort _) (β : α → Sort _)

namespace FunLike

variable {F α β} [i : FunLike F α β]

instance (priority := 100) hasCoeToFun : CoeFun F fun _ ↦ ∀ a : α, β a where coe := FunLike.coe

end FunLike

end Mathlib.Data.FunLike.Basic

section Mathlib.GroupTheory.GroupAction.Defs

instance (priority := 910) Mul.toSMul (α : Type _) [Mul α] : SMul α α :=
  ⟨(· * ·)⟩

class MulAction (α : Type _) (β : Type _) [Monoid α] extends SMul α β where

class IsScalarTower (M N α : Type _) [SMul M N] [SMul N α] [SMul M α] : Prop where

section

variable [Monoid M] [MulAction M α]

instance (priority := 910) Monoid.toMulAction : MulAction M M where
  smul := (· * ·)

end

class SMulZeroClass (M A : Type _) [Zero A] extends SMul M A where

class DistribSMul (M A : Type _) [AddZeroClass A] extends SMulZeroClass M A where

class DistribMulAction (M A : Type _) [Monoid M] [AddMonoid A] extends MulAction M A where

section

variable [Monoid M] [AddMonoid A] [DistribMulAction M A]

instance (priority := 100) DistribMulAction.toDistribSMul : DistribSMul M A :=
  { ‹DistribMulAction M A› with }

end

end Mathlib.GroupTheory.GroupAction.Defs

section Mathlib.Algebra.Group.Pi

variable {I : Type u}

variable {f : I → Type v}

namespace Pi

instance addSemigroup [∀ i, AddSemigroup <| f i] : AddSemigroup (∀ i : I, f i) :=
  { add := (· + ·)
    add_assoc := sorry
  }

instance addCommSemigroup [∀ i, AddCommSemigroup <| f i] : AddCommSemigroup (∀ i : I, f i) :=
  { addSemigroup with
    add_comm := sorry
  }

instance addZeroClass [∀ i, AddZeroClass <| f i] : AddZeroClass (∀ i : I, f i) :=
  { zero := (0 : ∀ i, f i)
    add := (· + ·)
    zero_add := sorry
    add_zero := sorry
  }

instance addMonoid [∀ i, AddMonoid <| f i] : AddMonoid (∀ i : I, f i) :=
  { addSemigroup, addZeroClass with
    nsmul := fun n x i => n • x i
    nsmul_zero := sorry
    nsmul_succ := sorry
  }

instance addCommMonoid [∀ i, AddCommMonoid <| f i] : AddCommMonoid (∀ i : I, f i) :=
  { addMonoid, addCommSemigroup with }

instance subNegMonoid [∀ i, SubNegMonoid <| f i] : SubNegMonoid (∀ i : I, f i) :=
  { addMonoid with
    neg := Neg.neg
    sub := Sub.sub
    zsmul := fun z x i => z • x i
    sub_eq_add_neg := sorry
    zsmul_zero' := sorry
    zsmul_succ' := sorry
    zsmul_neg' := sorry
  }

instance addGroup [∀ i, AddGroup <| f i] : AddGroup (∀ i : I, f i) :=
  { subNegMonoid with
    add_left_neg := sorry
    }

instance addCommGroup [∀ i, AddCommGroup <| f i] : AddCommGroup (∀ i : I, f i) :=
  { addGroup, addCommMonoid with }

end Pi

end Mathlib.Algebra.Group.Pi

section Mathlib.GroupTheory.Submonoid.Basic

structure AddSubmonoid (M : Type _) where

end Mathlib.GroupTheory.Submonoid.Basic

section Mathlib.Algebra.Hom.Ring

structure RingHom (α : Type _) (β : Type _) where
  toFun : α → β

infixr:25 " →+* " => RingHom

namespace RingHom

def id (α : Type _) : α →+* α := by
  refine { toFun := _root_.id.. }

def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
  { toFun := g.toFun ∘ f.toFun }

end RingHom

end Mathlib.Algebra.Hom.Ring

section Mathlib.Algebra.Module.Basic

class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where

instance (priority := 910) Semiring.toModule [Semiring R] : Module R R where

end Mathlib.Algebra.Module.Basic

section Mathlib.GroupTheory.Subgroup.Basic

structure AddSubgroup (G : Type _) [AddGroup G] extends AddSubmonoid G where

end Mathlib.GroupTheory.Subgroup.Basic

section Mathlib.Algebra.Quotient

class HasQuotient (A : outParam <| Type u) (B : Type v) where
  quotient' : B → Type max u v

@[reducible]
def HasQuotient.Quotient (A : outParam <| Type u) {B : Type v}
    [HasQuotient A B] (b : B) : Type max u v :=
  HasQuotient.quotient' b

notation:35 G " ⧸ " H:34 => HasQuotient.Quotient G H

end Mathlib.Algebra.Quotient

section Mathlib.Algebra.Module.Submodule.Basic

structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v
  extends AddSubmonoid M

def Submodule.toAddSubgroup [Ring R] [AddCommGroup M] {module_M : Module R M} (p : Submodule R M) : AddSubgroup M :=
  { p.toAddSubmonoid with }

end Mathlib.Algebra.Module.Submodule.Basic

section Mathlib.Data.Finsupp.Defs

structure Finsupp (α : Type _) (M : Type _) [Zero M] where
  toFun : α → M

infixr:25 " →₀ " => Finsupp

namespace Finsupp

instance funLike [Zero M] : FunLike (α →₀ M) α fun _ => M :=
  ⟨toFun⟩

instance zero [Zero M] : Zero (α →₀ M) :=
  ⟨⟨0⟩⟩

def single [Zero M] (a : α) (b : M) : α →₀ M where
  toFun :=
    have : DecidableEq α := sorry
    Pi.single a b

def onFinset [Zero M] (f : α → M) : α →₀ M where
  toFun := f

def mapRange [Zero M] [Zero N] (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  onFinset (f ∘ g)

def zipWith [Zero M] [Zero N] [Zero P] (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  onFinset
    (fun a => f (g₁ a) (g₂ a))

section AddZeroClass

variable [AddZeroClass M]

instance add : Add (α →₀ M) :=
  ⟨zipWith (· + ·) sorry⟩

end AddZeroClass

instance hasNatScalar [AddMonoid M] : SMul Nat (α →₀ M) :=
  ⟨fun n v => v.mapRange ((· • ·) n) sorry⟩

instance addCommMonoid [AddCommMonoid M] : AddCommMonoid (α →₀ M) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry

instance neg [NegZeroClass G] : Neg (α →₀ G) :=
  ⟨mapRange Neg.neg sorry⟩

instance sub [SubNegZeroMonoid G] : Sub (α →₀ G) :=
  ⟨zipWith Sub.sub sorry⟩

instance hasIntScalar [AddGroup G] : SMul Int (α →₀ G) :=
  ⟨fun n v => v.mapRange ((· • ·) n) sorry⟩

instance addCommGroup [AddCommGroup G] : AddCommGroup (α →₀ G) := {
  addCommMonoid with
  add_left_neg := sorry,
  sub_eq_add_neg := sorry,
}

end Finsupp

end Mathlib.Data.Finsupp.Defs

section Mathlib.Algebra.BigOperators.Finsupp

namespace Finsupp

def sum [Zero M] [AddCommMonoid N] (f : α →₀ M) (g : α → M → N) : N := 0

end Finsupp

end Mathlib.Algebra.BigOperators.Finsupp

section Mathlib.Data.Finsupp.Basic

namespace Finsupp

instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass R (α →₀ M) where
  smul a v := v.mapRange ((· • ·) a) sorry

end Finsupp

end Mathlib.Data.Finsupp.Basic

section Mathlib.Algebra.Algebra.Basic

class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A,
  R →+* A where

def algebraMap (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : R →+* A :=
  Algebra.toRingHom

def RingHom.toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S) : Algebra R S where
  smul c x := i.toFun c * x
  toRingHom := i

def RingHom.toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S) : Algebra R S :=
  i.toAlgebra'

namespace Algebra

variable {R : Type u}

section Semiring

variable [CommSemiring R]
variable [Semiring A] [Algebra R A]

instance (priority := 200) toModule : Module R A where

variable (R A)

instance id : Algebra R R :=
  (RingHom.id R).toAlgebra

end Semiring

end Algebra

end Mathlib.Algebra.Algebra.Basic

section Mathlib.Algebra.MonoidAlgebra.Basic

variable (k : Type u₁) (G : Type u₂)

section

variable [Semiring k]

def AddMonoidAlgebra :=
  G →₀ k

instance AddMonoidAlgebra.addCommMonoid : AddCommMonoid (AddMonoidAlgebra k G) :=
  inferInstanceAs (AddCommMonoid (G →₀ k))

end

namespace AddMonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

abbrev single (a : G) (b : k) : AddMonoidAlgebra k G := Finsupp.single a b

end

section Mul

variable [Semiring k] [Add G]

instance hasMul : Mul (AddMonoidAlgebra k G) :=
  ⟨fun f g => 0⟩

instance nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (AddMonoidAlgebra k G) :=
  { Finsupp.addCommMonoid with
    zero := 0
    mul := (· * ·)
    add := (· + ·)
    left_distrib := sorry
    right_distrib := sorry
    zero_mul := sorry
    mul_zero := sorry
    nsmul := fun n f => n • f
    nsmul_zero := sorry
    nsmul_succ := sorry }

end Mul

section One

variable [Semiring k] [Zero G] [NonAssocSemiring R]

instance one : One (AddMonoidAlgebra k G) :=
  ⟨single 0 1⟩

end One

instance nonUnitalSemiring [Semiring k] [AddSemigroup G] : NonUnitalSemiring (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.nonUnitalNonAssocSemiring with
    zero := 0
    mul := (· * ·)
    add := (· + ·)
    mul_assoc := sorry }

instance nonAssocSemiring [Semiring k] [AddZeroClass G] : NonAssocSemiring (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.nonUnitalNonAssocSemiring with
    one := 1
    mul := (· * ·)
    zero := 0
    add := (· + ·)
    one_mul := sorry
    mul_one := sorry }

instance smulZeroClass [Semiring k] [SMulZeroClass R k] : SMulZeroClass R (AddMonoidAlgebra k G) :=
  Finsupp.smulZeroClass

instance semiring [Semiring k] [AddMonoid G] : Semiring (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.nonUnitalSemiring,
    AddMonoidAlgebra.nonAssocSemiring with
    one := 1
    mul := (· * ·)
    zero := 0
    add := (· + ·) }

instance nonUnitalCommSemiring [CommSemiring k] [AddCommSemigroup G] :
    NonUnitalCommSemiring (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.nonUnitalSemiring with
    mul_comm := sorry }

instance commSemiring [CommSemiring k] [AddCommMonoid G] : CommSemiring (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.semiring, AddMonoidAlgebra.nonUnitalCommSemiring with }

instance addCommGroup [Ring k] : AddCommGroup (AddMonoidAlgebra k G) :=
  Finsupp.addCommGroup

instance nonUnitalNonAssocRing [Ring k] [Add G] : NonUnitalNonAssocRing (AddMonoidAlgebra k G) :=
  {  AddMonoidAlgebra.nonUnitalNonAssocSemiring, AddMonoidAlgebra.addCommGroup with }

instance nonUnitalRing [Ring k] [AddSemigroup G] : NonUnitalRing (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.addCommGroup, AddMonoidAlgebra.nonUnitalSemiring with }

instance nonAssocRing [Ring k] [AddZeroClass G] : NonAssocRing (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.nonAssocSemiring, AddMonoidAlgebra.addCommGroup with }

instance ring [Ring k] [AddMonoid G] : Ring (AddMonoidAlgebra k G) :=
  {  AddMonoidAlgebra.semiring, AddMonoidAlgebra.nonAssocRing with }

instance nonUnitalCommRing [CommRing k] [AddCommSemigroup G] :
    NonUnitalCommRing (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.nonUnitalRing, AddMonoidAlgebra.nonUnitalCommSemiring with }

instance commRing [CommRing k] [AddCommMonoid G] : CommRing (AddMonoidAlgebra k G) :=
  { AddMonoidAlgebra.ring, AddMonoidAlgebra.nonUnitalCommRing with }

end AddMonoidAlgebra

namespace AddMonoidAlgebra

variable {k G}

section Algebra

def singleZeroRingHom [Semiring k] [AddMonoid G] : k →+* AddMonoidAlgebra k G where
  toFun a := single 0 a

instance algebra [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
    Algebra R (AddMonoidAlgebra k G) :=
  { singleZeroRingHom.comp (algebraMap R k) with }

end Algebra

end AddMonoidAlgebra

end Mathlib.Algebra.MonoidAlgebra.Basic

section Mathlib.RingTheory.Ideal.Basic

@[reducible]
def Ideal (R : Type u) [Semiring R] := Submodule R R

end Mathlib.RingTheory.Ideal.Basic

section Mathlib.GroupTheory.Congruence

open Function Setoid

structure AddCon (M : Type _) [Add M] extends Setoid M where

structure Con (M : Type _) [Mul M] extends Setoid M where

protected def Con.Quotient [Mul M] (c : Con M) :=
  Quotient c.toSetoid

protected def AddCon.Quotient [Add M] (c : AddCon M) :=
  Quotient c.toSetoid

def Con.toQuotient [Mul M] {c : Con M} : M → c.Quotient :=
  Quotient.mk''

def AddCon.toQuotient [Add M] {c : AddCon M} : M → c.Quotient :=
  Quotient.mk''

instance (priority := 10) [Mul M] {c : Con M} : CoeTC M c.Quotient :=
  ⟨Con.toQuotient⟩

instance (priority := 10) [Add M] {c : AddCon M} : CoeTC M c.Quotient :=
  ⟨AddCon.toQuotient⟩

instance hasMul [Mul M] {c : Con M} : Mul c.Quotient :=
  ⟨Quotient.map₂' (· * ·) sorry⟩

instance hasAdd [Add M] {c : AddCon M} : Add c.Quotient :=
  ⟨Quotient.map₂' (· + ·) sorry⟩

instance mulOneClass [MulOneClass M] (c : Con M) : MulOneClass c.Quotient
    where
  one := ((1 : M) : c.Quotient)
  mul := (· * ·)
  mul_one x := sorry
  one_mul x := sorry

instance addZeroClass [AddZeroClass M] (c : AddCon M) : AddZeroClass c.Quotient where
  zero := ((0 : M) : c.Quotient)
  add := (· + ·)
  add_zero x := sorry
  zero_add x := sorry

instance [Monoid M] (c : Con M) : Pow c.Quotient Nat
    where pow x n := Quotient.map' (fun x => x ^ n) (fun _ _ => sorry) x

instance hasNeg [AddGroup M] (c : AddCon M) : Neg c.Quotient :=
  ⟨(Quotient.map' Neg.neg) fun _ _ => sorry⟩

instance hasSub [AddGroup M] (c : AddCon M) : Sub c.Quotient :=
  ⟨(Quotient.map₂' (· - ·)) fun _ _ h₁ _ _ h₂ => sorry⟩

instance instSMul [MulOneClass M] [SMul α M] (c : Con M) :
    SMul α c.Quotient where
  smul a := (Quotient.map' ((· • ·) a)) fun _ _ => sorry

end Mathlib.GroupTheory.Congruence

section Mathlib.GroupTheory.Coset

def QuotientAddGroup.leftRel [AddGroup α] (s : AddSubgroup α) : Setoid α :=
  sorry

end Mathlib.GroupTheory.Coset

section Mathlib.GroupTheory.QuotientGroup

protected def QuotientAddGroup.con [AddGroup G] (N : AddSubgroup G) : AddCon G where
  toSetoid := leftRel N

end Mathlib.GroupTheory.QuotientGroup

section Mathlib.LinearAlgebra.Quotient

namespace Submodule

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)

open QuotientAddGroup

def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup

instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩

namespace Quotient

def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''

variable {S : Type _} [SMul S R] [SMul S M] [IsScalarTower S R M] (P : Submodule R M)

instance instSMul' : SMul S (M ⧸ P) :=
  ⟨fun a => Quotient.map' ((· • ·) a) fun x y h => sorry⟩

end Quotient

end Submodule

end Mathlib.LinearAlgebra.Quotient

section Mathlib.RingTheory.Congruence

structure RingCon (R : Type _) [Add R] [Mul R] extends Setoid R where

variable {α R : Type _}

namespace RingCon

section Basic

variable [Add R] [Mul R] (c : RingCon R)

def toAddCon : AddCon R :=
  { c with }

def toCon : Con R :=
  { c with }

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

protected def Quotient :=
  Quotient c.toSetoid

variable {c}

def toQuotient (r : R) : c.Quotient :=
  @Quotient.mk'' _ c.toSetoid r

variable (c)

instance : CoeTC R c.Quotient :=
  ⟨toQuotient⟩

end Basic

section add_mul

variable [Add R] [Mul R] (c : RingCon R)

instance : Add c.Quotient := inferInstanceAs (Add c.toAddCon.Quotient)

instance : Mul c.Quotient := inferInstanceAs (Mul c.toCon.Quotient)

end add_mul

section Zero

variable [AddZeroClass R] [Mul R] (c : RingCon R)

instance : Zero c.Quotient := inferInstanceAs (Zero c.toAddCon.Quotient)

end Zero

section One

variable [Add R] [MulOneClass R] (c : RingCon R)

instance : One c.Quotient := inferInstanceAs (One c.toCon.Quotient)

end One

section SMul

variable [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R] (c : RingCon R)

instance : SMul α c.Quotient := inferInstanceAs (SMul α c.toCon.Quotient)

end SMul

section NegSubZsmul

variable [AddGroup R] [Mul R] (c : RingCon R)

instance : Neg c.Quotient := inferInstanceAs (Neg c.toAddCon.Quotient)

instance : Sub c.Quotient := inferInstanceAs (Sub c.toAddCon.Quotient)

end NegSubZsmul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

instance : Pow c.Quotient Nat := inferInstanceAs (Pow c.toCon.Quotient Nat)

end Pow

instance [CommRing R] (c : RingCon R) : CommRing c.Quotient :=
  sorry

end Quotient

end RingCon

end Mathlib.RingTheory.Congruence

section Mathlib.RingTheory.Ideal.Quotient

namespace Ideal.Quotient

variable [CommRing R]

/-- On `Ideal`s, `Submodule.quotientRel` is a ring congruence. -/
protected def ringCon (I : Ideal R) : RingCon R :=
  { QuotientAddGroup.con I.toAddSubgroup with }

instance commRing (I : Ideal R) : CommRing (R ⧸ I) :=
    inferInstanceAs (CommRing (Quotient.ringCon I).Quotient)

/-- The ring homomorphism from a ring `R` to a quotient ring `R/I`. -/
def mk (I : Ideal R) : R →+* R ⧸ I where
  toFun a := Submodule.Quotient.mk a

end Ideal.Quotient

end Mathlib.RingTheory.Ideal.Quotient

section Mathlib.Algebra.RingQuot

universe uR uS uA

variable {R : Type uR} [Semiring R]
variable {S : Type uS} [CommSemiring S]
variable {A : Type uA} [Semiring A] [Algebra S A]

namespace RingQuot

/-- Given an arbitrary relation `r` on a ring, we strengthen it to a relation `Rel r`,
such that the equivalence relation generated by `Rel r` has `x ~ y` if and only if
`x - y` is in the ideal generated by elements `a - b` such that `r a b`.
-/
inductive Rel (r : R → R → Prop) : R → R → Prop
  | of ⦃x y : R⦄ (h : r x y) : Rel r x y
  | add_left ⦃a b c⦄ : Rel r a b → Rel r (a + c) (b + c)
  | mul_left ⦃a b c⦄ : Rel r a b → Rel r (a * c) (b * c)
  | mul_right ⦃a b c⦄ : Rel r b c → Rel r (a * b) (a * c)

end RingQuot

/-- The quotient of a ring by an arbitrary relation. -/
structure RingQuot (r : R → R → Prop) where
  toQuot : Quot (RingQuot.Rel r)

namespace RingQuot

variable (r : R → R → Prop)

private def zero : RingQuot r :=
  ⟨Quot.mk _ 0⟩

private def one : RingQuot r :=
  ⟨Quot.mk _ 1⟩

private def add : RingQuot r → RingQuot r → RingQuot r
  | ⟨a⟩, ⟨b⟩ => ⟨Quot.map₂ (· + ·) sorry sorry a b⟩

private def mul : RingQuot r → RingQuot r → RingQuot r
  | ⟨a⟩, ⟨b⟩ => ⟨Quot.map₂ (· * ·) sorry sorry a b⟩

private def neg {R : Type uR} [Ring R] (r : R → R → Prop) : RingQuot r → RingQuot r
  | ⟨a⟩ => ⟨Quot.map (fun a ↦ -a) sorry a⟩

private def sub {R : Type uR} [Ring R] (r : R → R → Prop) :
  RingQuot r → RingQuot r → RingQuot r
  | ⟨a⟩, ⟨b⟩ => ⟨Quot.map₂ Sub.sub sorry sorry a b⟩

private def npow (n : Nat) : RingQuot r → RingQuot r
  | ⟨a⟩ =>
    ⟨Quot.lift (fun a ↦ Quot.mk (RingQuot.Rel r) (a ^ n))
        (fun a b (h : Rel r a b) ↦ sorry)
        a⟩

private def smul [Algebra S R] (n : S) : RingQuot r → RingQuot r
  | ⟨a⟩ => ⟨Quot.map (fun a ↦ n • a) sorry a⟩

instance : Zero (RingQuot r) :=
  ⟨zero r⟩

instance : One (RingQuot r) :=
  ⟨one r⟩

instance : Add (RingQuot r) :=
  ⟨add r⟩

instance : Mul (RingQuot r) :=
  ⟨mul r⟩

instance : Pow (RingQuot r) Nat :=
  ⟨fun x n ↦ npow r n x⟩

instance {R : Type uR} [Ring R] (r : R → R → Prop) : Neg (RingQuot r) :=
  ⟨neg r⟩

instance {R : Type uR} [Ring R] (r : R → R → Prop) : Sub (RingQuot r) :=
  ⟨sub r⟩

instance [Algebra S R] : SMul S (RingQuot r) :=
  ⟨smul r⟩

instance instAddCommMonoid (r : R → R → Prop) : AddCommMonoid (RingQuot r) where
  add := (· + ·)
  zero := 0
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry

instance instMonoidWithZero (r : R → R → Prop) : MonoidWithZero (RingQuot r) where
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  zero_mul := sorry
  mul_zero := sorry
  npow n x := x ^ n
  npow_zero := sorry
  npow_succ := sorry

instance instSemiring (r : R → R → Prop) : Semiring (RingQuot r) :=
  { instAddCommMonoid r, instMonoidWithZero r with
    left_distrib := sorry
    right_distrib := sorry
    nsmul := (· • ·)
    nsmul_zero := sorry
    nsmul_succ := sorry }

instance instRing {R : Type uR} [Ring R] (r : R → R → Prop) : Ring (RingQuot r) :=
  { RingQuot.instSemiring r with
    neg := Neg.neg
    add_left_neg := sorry
    sub := Sub.sub
    sub_eq_add_neg := sorry
    zsmul := sorry
    zsmul_zero' := sorry
    zsmul_succ' := sorry
    zsmul_neg' := sorry }

instance instCommSemiring {R : Type uR} [CommSemiring R] (r : R → R → Prop) :
  CommSemiring (RingQuot r) :=
  { RingQuot.instSemiring r with
    mul_comm := sorry }

instance {R : Type uR} [CommRing R] (r : R → R → Prop) : CommRing (RingQuot r) :=
  { RingQuot.instRing r, RingQuot.instCommSemiring r with }

instance instAlgebraRingQuot [Algebra S R] (r : R → R → Prop) : Algebra S (RingQuot r) where
  smul := (· • ·)
  toFun r := ⟨Quot.mk _ ((algebraMap S R).toFun r)⟩

end RingQuot

end Mathlib.Algebra.RingQuot

section Mathlib.RingTheory.Ideal.QuotientOperations

namespace Ideal

variable (R₁ : Type _) {A : Type _} [CommSemiring R₁] [CommRing A] [Algebra R₁ A]

instance Quotient.algebra {I : Ideal A} : Algebra R₁ (A ⧸ I) :=
  { toRingHom :=  RingHom.comp (Ideal.Quotient.mk I) (algebraMap R₁ A) }

end Ideal

end Mathlib.RingTheory.Ideal.QuotientOperations

open Function Finsupp AddMonoidAlgebra
open Ideal.Quotient Ideal RingQuot

section Mathlib.Data.Nat.Basic

instance : Semiring Nat := sorry

end Mathlib.Data.Nat.Basic

section Mathlib.Data.MvPolynomial.Basic

def MvPolynomial (σ : Type _) (R : Type _) [CommSemiring R] :=
  AddMonoidAlgebra R (σ → Nat)

namespace MvPolynomial

instance commSemiring [CommSemiring R] : CommSemiring (MvPolynomial σ R) :=
  AddMonoidAlgebra.commSemiring

instance algebra [CommSemiring R] [CommSemiring S₁] [Algebra R S₁] :
    Algebra R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.algebra

end MvPolynomial

end Mathlib.Data.MvPolynomial.Basic

section Mathlib.Data.MvPolynomial.CommRing

instance instCommRingMvPolynomial [CommRing R] : CommRing (MvPolynomial σ R) :=
  AddMonoidAlgebra.commRing

end Mathlib.Data.MvPolynomial.CommRing

variable (R : Type u) [CommSemiring R] (M : Type v)

inductive r : (MvPolynomial M R) → (MvPolynomial M R) → Prop

def Quot_r := RingQuot (r R M)

instance : Semiring (Quot_r R M) :=
  RingQuot.instSemiring _

instance {S : Type w} [CommRing S] : CommRing (Quot_r S M) :=
  RingQuot.instCommRing _

instance instAlgebra
    {R A M} [CommSemiring R] [CommRing A] [Algebra R A] :
    Algebra R (Quot_r A M) :=
  RingQuot.instAlgebraRingQuot _

--------------

/-!
Typeclass synthesis should remain fast when multiple `with` patterns are nested

Prior to #2478, this requires over 30000 heartbeats.
-/
set_option synthInstance.maxHeartbeats 400 in
instance instAlgebra' (R M : Type _) [CommRing R] (I : Ideal (Quot_r R M)) :
    Algebra R ((Quot_r R M) ⧸ I) := inferInstance
