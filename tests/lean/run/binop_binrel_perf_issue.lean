/-!
This is a minimization of an `isDefEq` timeout from Mathlib.Algebra.Module.Submodule.Localization,
where it is reasonably fast with `set_option backward.isDefEq.lazyWhnfCore false`,
but very slow with the default `isDefEq` algorithm.
-/

section Mathlib.Init.Set

set_option autoImplicit true

def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α := p

namespace Set

protected def Mem (s : Set α) (a : α) : Prop := s a

instance : Membership α (Set α) := ⟨Set.Mem⟩

end Set

end Mathlib.Init.Set

section Mathlib.Init.Function

universe u₁ u₂

variable {α : Sort u₁} {β : Sort u₂}

def Function.Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

def Function.Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

end Mathlib.Init.Function

section Mathlib.Data.Subtype

variable {α : Sort _} {p : α → Prop}

theorem Subtype.coe_injective : Function.Injective (fun (a : Subtype p) ↦ (a : α)) := fun _ _ ↦ Subtype.ext

end Mathlib.Data.Subtype

section Mathlib.Data.Set.Defs

universe u v w

namespace Set

variable {α : Type u} {β : Type v}

def preimage (f : α → β) (s : Set β) : Set α := setOf fun x => f x ∈ s

infixl:80 " ⁻¹' " => preimage

variable {ι : Sort _} {f : ι → α}

def range (f : ι → α) : Set α := setOf fun x => ∃ y, f y = x

end Set

end Mathlib.Data.Set.Defs

section Mathlib.Data.FunLike.Basic

class DFunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  coe : F → ∀ a : α, β a

abbrev FunLike F α β := DFunLike F α fun _ => β

namespace DFunLike

variable {F α β} [i : DFunLike F α β]

instance (priority := 100) hasCoeToFun : CoeFun F (fun _ ↦ ∀ a : α, β a) where
  coe := @DFunLike.coe _ _ β _

end DFunLike

end Mathlib.Data.FunLike.Basic

section Mathlib.Logic.Relator

universe u₁ u₂ v₁ v₂

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variable (R : α → β → Prop) (S : γ → δ → Prop)

def LiftFun (f : α → γ) (g : β → δ) : Prop :=
  ∀⦃a b⦄, R a b → S (f a) (g b)

infixr:40 " ⇒ " => LiftFun

end Mathlib.Logic.Relator

section Mathlib.Data.Quot

variable {α : Sort _} {β : Sort _}

namespace Quotient

variable {γ : Sort _} {φ : Sort _} {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

protected def mk'' (a : α) : Quotient s₁ :=
  Quot.mk s₁.1 a

theorem surjective_Quotient_mk'' : Function.Surjective (Quotient.mk'' : α → Quotient s₁) :=
  Quot.exists_rep

protected def liftOn' (q : Quotient s₁) (f : α → φ) (h : ∀ a b, @Setoid.r α s₁ a b → f a = f b) :
    φ :=
  Quotient.liftOn q f h

protected def map' (f : α → β) (h : (s₁.r ⇒ s₂.r) f f) : Quotient s₁ → Quotient s₂ :=
  (Quot.lift fun x ↦ Quot.mk _ (f x)) fun _ _ h₁ ↦ Quot.sound <| h h₁

protected def map₂' (f : α → β → γ) (h : (s₁.r ⇒ s₂.r ⇒ s₃.r) f f) :
    Quotient s₁ → Quotient s₂ → Quotient s₃ :=
  Quotient.lift₂ (fun x y ↦ Quotient.mk _ (f x y)) fun _ _ _ _ h₁ h₂ ↦ Quot.sound <| h h₁ h₂

end Quotient

end Mathlib.Data.Quot

section Mathlib.Data.SetLike.Basic

class SetLike (A : Type _) (B : outParam <| Type _) where
  protected coe : A → Set B

namespace SetLike

variable {A : Type _} {B : Type _} [i : SetLike A B]

instance : CoeTC A (Set B) where coe := SetLike.coe

instance (priority := 100) instMembership : Membership B A :=
  ⟨fun p x => x ∈ (p : Set B)⟩

instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

end SetLike

end Mathlib.Data.SetLike.Basic

section Mathlib.Algebra.Group.Defs

universe u v w

class HVAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hVAdd : α → β → γ

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

class VAdd (G : Type u) (P : Type v) where
  vadd : G → P → P

class SMul (M : Type u) (α : Type v) where
  smul : M → α → α

infixl:65 " +ᵥ " => HVAdd.hVAdd
infixr:73 " • " => HSMul.hSMul

macro_rules | `($x • $y) => `(leftact% HSMul.hSMul $x $y)

instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

instance instHVAdd {α β} [VAdd α β] : HVAdd α β β where
  hVAdd := VAdd.vadd

class AddSemigroup (G : Type u) extends Add G where
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

class MulOneClass (M : Type u) extends One M, Mul M where

class AddZeroClass (M : Type u) extends Zero M, Add M where
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a


class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  protected nsmul : Nat → M → M

instance AddMonoid.toNatSMul {M : Type _} [AddMonoid M] : SMul Nat M :=
  ⟨AddMonoid.nsmul⟩

class AddCommMonoid (M : Type u) extends AddMonoid M

def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub := SubNegMonoid.sub'
  protected zsmul : Int → G → G

instance SubNegMonoid.SMulInt {M} [SubNegMonoid M] : SMul Int M :=
  ⟨SubNegMonoid.zsmul⟩

class AddGroup (A : Type u) extends SubNegMonoid A where
  protected add_left_neg : ∀ a : A, -a + a = 0

class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.Opposites

variable {α : Type _}

structure PreOpposite (α : Type _) : Type _ where
  op' ::
  unop' : α

def MulOpposite (α : Type _) : Type _ := PreOpposite α
def AddOpposite (α : Type _) : Type _ := PreOpposite α

postfix:max "ᵐᵒᵖ" => MulOpposite

postfix:max "ᵃᵒᵖ" => AddOpposite

namespace MulOpposite

def unop : αᵐᵒᵖ → α :=
  PreOpposite.unop'

end MulOpposite

namespace AddOpposite

def op : α → αᵃᵒᵖ :=
  PreOpposite.op'

def unop : αᵃᵒᵖ → α :=
  PreOpposite.unop'

instance instZero [Zero α] : Zero αᵃᵒᵖ where zero := op 0
instance instAdd [Add α] : Add αᵃᵒᵖ where add x y := op (unop y + unop x)
instance instNeg [Neg α] : Neg αᵃᵒᵖ where neg x := op <| -(unop x)

end AddOpposite

end Mathlib.Algebra.Opposites

section Mathlib.Algebra.Group.Hom.Defs

variable {M N A B : Type _}

structure AddMonoidHom (M : Type _) (N : Type _) [Add M] [Add N] where
  protected toFun : M → N

infixr:25 " →+ " => AddMonoidHom

structure MonoidHom (M : Type _) (N : Type _) [Mul M] [Mul N] where
  protected toFun : M → N

infixr:25 " →* " => MonoidHom

instance MonoidHom.instFunLike [Mul M] [Mul N] : FunLike (M →* N) M N where
  coe f := f.toFun

instance AddMonoidHom.instFunLike [Add A] [Add B] : FunLike (A →+ B) A B where
  coe f := f.toFun

end Mathlib.Algebra.Group.Hom.Defs

section Mathlib.GroupTheory.GroupAction.Defs

variable {M N α : Type _}

instance (priority := 910) Mul.toSMul (α : Type _) [Mul α] : SMul α α :=
  ⟨(· * ·)⟩

namespace SMul

variable [SMul M α]

def comp.smul (g : N → M) (n : N) (a : α) : α :=
  g n • a

variable (α)

def comp (g : N → M) : SMul N α where smul := SMul.comp.smul g

end SMul

namespace VAdd

variable [VAdd M α]

def comp.vadd (g : N → M) (n : N) (a : α) : α :=
  g n +ᵥ a

end VAdd

variable [AddMonoid M] [VAdd M α]

namespace VAdd

variable (α)

def compHom [AddMonoid N] (g : N →+ M) : VAdd N α where
  vadd := VAdd.comp.vadd g

end VAdd

end Mathlib.GroupTheory.GroupAction.Defs

section Mathlib.GroupTheory.Subsemigroup.Basic

class MulMemClass (S : Type _) (M : Type _) [Mul M] [SetLike S M] : Prop where

class AddMemClass (S : Type _) (M : Type _) [Add M] [SetLike S M] : Prop where

structure Subsemigroup (M : Type _) [Mul M] where
  carrier : Set M

structure AddSubsemigroup (M : Type _) [Add M] where
  carrier : Set M

end Mathlib.GroupTheory.Subsemigroup.Basic

section Mathlib.Algebra.Group.InjSurj

namespace Function

namespace Injective

variable {M₁ : Type _} {M₂ : Type _}

protected def mulOneClass [Mul M₁] [One M₁] [MulOneClass M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₁ :=
  { ‹One M₁›, ‹Mul M₁› with }

variable [Add M₁] [Zero M₁]

protected def addZeroClass [AddZeroClass M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) : AddZeroClass M₁ :=
  { ‹Zero M₁›, ‹Add M₁› with
    zero_add := sorry,
    add_zero := sorry }

protected def addSemigroup [AddSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) : AddSemigroup M₁ :=
  { ‹Add M₁› with add_assoc := sorry }

variable [SMul Nat M₁]

protected def addMonoid [AddMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : Nat), f (n • x) = n • f x) : AddMonoid M₁ :=
  { hf.addZeroClass f zero add, hf.addSemigroup f add with
    nsmul := fun n x => n • x }

end Injective

namespace Surjective

variable {M₁ : Type _} {M₂ : Type _} [Add M₂]

protected def addSemigroup [AddSemigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (add : ∀ x y, f (x + y) = f x + f y) : AddSemigroup M₂ :=
  { ‹Add M₂› with add_assoc := sorry }

variable [Zero M₂]

protected def addZeroClass [AddZeroClass M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) : AddZeroClass M₂ :=
  { ‹Zero M₂›, ‹Add M₂› with
    zero_add := sorry,
    add_zero := sorry }

variable [SMul Nat M₂]

protected def addMonoid [AddMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : Nat), f (n • x) = n • f x) : AddMonoid M₂ :=
  { hf.addSemigroup f add, hf.addZeroClass f zero add with
    nsmul := fun n x => n • x }

variable [Neg M₂] [Sub M₂] [SMul Int M₂]

protected def subNegMonoid [SubNegMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y)
    (nsmul : ∀ (x) (n : Nat), f (n • x) = n • f x) : SubNegMonoid M₂ :=
  { hf.addMonoid f zero add nsmul, ‹Sub M₂›, ‹Neg M₂› with
    zsmul := fun n x => n • x }

protected def addGroup [AddGroup M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y)
    (nsmul : ∀ (x) (n : Nat), f (n • x) = n • f x) : AddGroup M₂ :=
  { hf.subNegMonoid f zero add nsmul with
    add_left_neg := sorry }

end Surjective

end Function


end Mathlib.Algebra.Group.InjSurj

section Mathlib.Algebra.Group.Opposite

variable {α : Type _}

namespace AddOpposite

instance instAddSemigroup [AddSemigroup α] : AddSemigroup αᵃᵒᵖ where
  add_assoc x y z := sorry

instance instAddZeroClass [AddZeroClass α] : AddZeroClass αᵃᵒᵖ where
  toAdd := instAdd
  toZero := instZero
  zero_add _ := sorry
  add_zero _ := sorry

instance instAddMonoid [AddMonoid α] : AddMonoid αᵃᵒᵖ :=
  { instAddZeroClass with
    toAddSemigroup := instAddSemigroup
    nsmul := fun n a => op <| n • a.unop }

instance instSubNegMonoid [SubNegMonoid α] : SubNegMonoid αᵃᵒᵖ where
  toAddMonoid := instAddMonoid
  toNeg := instNeg
  zsmul n a := op <| n • a.unop

instance instAddGroup [AddGroup α] : AddGroup αᵃᵒᵖ where
  toSubNegMonoid := instSubNegMonoid
  add_left_neg _ := sorry

end AddOpposite

end Mathlib.Algebra.Group.Opposite

section Mathlib.GroupTheory.Subsemigroup.Operations

variable {M : Type _}

namespace MulMemClass

variable {A : Type _} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, sorry⟩⟩

end MulMemClass

namespace AddMemClass

variable {A : Type _} [Add M] [SetLike A M] [hA : AddMemClass A M] (S' : A)

instance (priority := 900) add : Add S' :=
  ⟨fun a b => ⟨a.1 + b.1, sorry⟩⟩

end AddMemClass

end Mathlib.GroupTheory.Subsemigroup.Operations

section Mathlib.GroupTheory.Submonoid.Basic

variable {M : Type _} {N : Type _}
variable {A : Type _}

variable [MulOneClass M] {s : Set M}
variable [AddZeroClass A] {t : Set A}

structure Submonoid (M : Type _) [MulOneClass M] extends Subsemigroup M where

class SubmonoidClass (S : Type _) (M : Type _) [MulOneClass M] [SetLike S M] : Prop extends
  MulMemClass S M

structure AddSubmonoid (M : Type _) [AddZeroClass M] extends AddSubsemigroup M where

class AddSubmonoidClass (S : Type _) (M : Type _) [AddZeroClass M] [SetLike S M] : Prop extends
  AddMemClass S M

namespace AddSubmonoid

instance : SetLike (AddSubmonoid A) A where
  coe s := s.carrier

instance : AddSubmonoidClass (AddSubmonoid A) A where

end AddSubmonoid

namespace Submonoid

instance : SetLike (Submonoid M) M where
  coe s := s.carrier

instance : SubmonoidClass (Submonoid M) M where

end Submonoid

end Mathlib.GroupTheory.Submonoid.Basic

section Mathlib.GroupTheory.Submonoid.Operations

variable {M : Type _} [MulOneClass M] (S : Submonoid M)
variable {B : Type _} [AddZeroClass B] (T : AddSubmonoid B)

section

variable {A M₁ : Type _} [SetLike A M₁] (S' : A)

instance one [One M₁] : One S' :=
  ⟨⟨1, sorry⟩⟩

instance zero [Zero M₁] : Zero S' :=
  ⟨⟨0, sorry⟩⟩

end

namespace AddSubmonoidClass

instance nSMul {M} [AddMonoid M] {A : Type _} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : SMul Nat S :=
  ⟨fun n a => ⟨n • a.1, sorry⟩⟩

end AddSubmonoidClass

namespace SubmonoidClass

instance (priority := 75) toMulOneClass {M : Type _} [MulOneClass M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : MulOneClass S :=
    Subtype.coe_injective.mulOneClass Subtype.val sorry sorry

instance (priority := 75) toAddMonoid {M : Type _} [AddMonoid M] {A : Type _} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : AddMonoid S :=
  Subtype.coe_injective.addMonoid Subtype.val sorry sorry sorry

end SubmonoidClass

namespace AddSubmonoid

def subtype : T →+ B where
  toFun := Subtype.val

end AddSubmonoid

namespace Submonoid

def subtype : S →* M where
  toFun := Subtype.val

end Submonoid

namespace Submonoid

variable {M' : Type _} {α : Type _}

section MulOneClass

variable [MulOneClass M']

instance smul [SMul M' α] (S : Submonoid M') : SMul S α :=
  SMul.comp _ S.subtype

end MulOneClass

variable [AddMonoid M']

instance vadd [VAdd M' α] (S : AddSubmonoid M') : VAdd S α :=
  VAdd.compHom _ S.subtype

end Submonoid

end Mathlib.GroupTheory.Submonoid.Operations

section Mathlib.GroupTheory.Congruence

variable (M : Type _) {N : Type _} {P : Type _}

structure AddCon [Add M] extends Setoid M where

variable {M}

namespace AddCon

section

variable [Add M] (c : AddCon M)

protected def Quotient :=
  Quotient c.toSetoid

protected def liftOn {β} {c : AddCon M} (q : c.Quotient) (f : M → β) (h : ∀ a b, c.r a b → f a = f b) :
    β :=
  Quotient.liftOn' q f h

instance hasAdd : Add c.Quotient :=
  ⟨Quotient.map₂' (· + ·) sorry⟩

end

section AddZeroClass

variable [AddZeroClass M] [AddZeroClass P] (c : AddCon M)

variable (f : M →+ P)

def lift : c.Quotient →+ P where
  toFun x := (AddCon.liftOn x f) sorry

end AddZeroClass

section Monoids

instance zero [AddZeroClass M] (c : AddCon M) : Zero c.Quotient where
  zero := Quotient.mk'' (0 : M)

instance _root_.AddCon.Quotient.nsmul {M : Type _} [AddMonoid M] (c : AddCon M) :
    SMul Nat c.Quotient where
  smul n := (Quotient.map' (n • ·)) sorry

instance addSemigroup {M : Type _} [AddSemigroup M] (c : AddCon M) : AddSemigroup c.Quotient :=
  { (Function.Surjective.addSemigroup _ Quotient.surjective_Quotient_mk'' sorry :
      AddSemigroup c.Quotient) with
    toAdd := AddCon.hasAdd _ }

instance addMonoid {M : Type _} [AddMonoid M] (c : AddCon M) : AddMonoid c.Quotient :=
  { (Function.Surjective.addMonoid _ Quotient.surjective_Quotient_mk'' sorry sorry sorry : AddMonoid c.Quotient) with
    toAddSemigroup := AddCon.addSemigroup _
    toZero := AddCon.zero _ }

end Monoids

variable [AddGroup M] [AddGroup N] [AddGroup P] (c : AddCon M)

instance hasNeg : Neg c.Quotient :=
  ⟨(Quotient.map' Neg.neg) sorry⟩

instance hasSub : Sub c.Quotient :=
  ⟨(Quotient.map₂' (· - ·)) sorry⟩

instance _root_.AddCon.Quotient.zsmul {M : Type _} [AddGroup M] (c : AddCon M) :
    SMul Int c.Quotient :=
  ⟨fun z => (Quotient.map' (z • ·)) sorry⟩

instance addGroup : AddGroup c.Quotient :=
  { (Function.Surjective.addGroup Quotient.mk''
      Quotient.surjective_Quotient_mk'' sorry sorry sorry : AddGroup c.Quotient) with
    toAddMonoid := AddCon.addMonoid _
    toNeg := AddCon.hasNeg _
    toSub := AddCon.hasSub _ }

end AddCon

end Mathlib.GroupTheory.Congruence

section Mathlib.GroupTheory.GroupAction.Opposite

variable {α}

instance Add.toHasOppositeVAdd [Add α] : VAdd αᵃᵒᵖ α :=
  ⟨fun c x => x + c.unop⟩

instance AddMonoid.toOppositeVAdd [AddMonoid α] : VAdd αᵃᵒᵖ α where
  vadd := (· +ᵥ ·)

end Mathlib.GroupTheory.GroupAction.Opposite

section Mathlib.GroupTheory.Subgroup.Basic

variable {A : Type _} [AddGroup A]

structure AddSubgroup (G : Type _) [AddGroup G] extends AddSubmonoid G where

namespace AddSubgroup

instance : SetLike (AddSubgroup A) A where
  coe s := s.carrier

end AddSubgroup

end Mathlib.GroupTheory.Subgroup.Basic

section Mathlib.GroupTheory.GroupAction.Basic

universe u v

namespace VAdd

variable (M : Type u) [AddMonoid M] {α : Type v} [VAdd M α]

def orbit (a : α) :=
  Set.range fun m : M => m +ᵥ a

variable (G α : Type _) [AddGroup G] [VAdd G α]

def orbitRel : Setoid α where
  r a b := a ∈ orbit G b
  iseqv := sorry

end VAdd

end Mathlib.GroupTheory.GroupAction.Basic

section Mathlib.GroupTheory.Subgroup.MulOpposite

variable {G : Type _} [AddGroup G]

protected def AddSubgroup.op (H : AddSubgroup G) : AddSubgroup Gᵃᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' (H : Set G)

end Mathlib.GroupTheory.Subgroup.MulOpposite

section Mathlib.Algebra.Quotient

universe u v

class HasQuotient (A : outParam <| Type u) (B : Type v) where
  quotient' : B → Type max u v

def HasQuotient.Quotient (A : outParam <| Type u) {B : Type v}
    [HasQuotient A B] (b : B) : Type max u v :=
  HasQuotient.quotient' b

notation:35 G " ⧸ " H:34 => HasQuotient.Quotient G H

end Mathlib.Algebra.Quotient

section Mathlib.GroupTheory.Coset

variable {α : Type _}

namespace QuotientAddGroup

variable [AddGroup α] (s : AddSubgroup α)

instance : VAdd s.op α := Submonoid.vadd s.op.toAddSubmonoid

def leftRel : Setoid α :=
  VAdd.orbitRel s.op α

instance instHasQuotientAddSubgroup : HasQuotient α (AddSubgroup α) :=
  ⟨fun s => Quotient (leftRel s)⟩

end QuotientAddGroup

end Mathlib.GroupTheory.Coset

section Mathlib.Algebra.Module.LinearMap.Basic

open Function

universe u u' v w x y z

variable {R R₁ R₂ R₃ k S M M₁ M₂ M₃ : Type _}

structure LinearMap (R : Type _) [Mul R] (M : Type _)
    (M₂ : Type _) [AddCommMonoid M] [AddCommMonoid M₂] [SMul R M] [SMul R M₂] extends
    AddMonoidHom M M₂

notation:25 M " →ₗ[" R:25 "] " M₂:0 => LinearMap R M M₂

namespace LinearMap

section AddCommMonoid

variable [Mul R] [Mul S]

section

variable [AddCommMonoid M] [AddCommMonoid M₃]
variable [SMul R M] [SMul R M₃]

instance instFunLike : FunLike (M →ₗ[R] M₃) M M₃ where
  coe f := f.toFun

end

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M₁ : SMul R M₁} {module_M₂ : SMul R M₂} {module_M₃ : SMul R M₃}
variable (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂)

def comp : M₁ →ₗ[R] M₃ where
  toFun := f ∘ g

end

end AddCommMonoid

end LinearMap

end Mathlib.Algebra.Module.LinearMap.Basic

section Mathlib.Algebra.Module.Submodule.Basic

universe u v

variable {R : Type u} {M : Type v}

structure Submodule (R : Type u) (M : Type v) [Mul R] [AddCommMonoid M] [SMul R M] : Type v
  extends AddSubmonoid M

instance setLike [Mul R] [AddCommMonoid M] [SMul R M] : SetLike (Submodule R M) M where
  coe s := s.carrier

def Submodule.toAddSubgroup [Mul R] [AddCommGroup M] {module_M : SMul R M} (p : Submodule R M) : AddSubgroup M :=
  { p.toAddSubmonoid with }

end Mathlib.Algebra.Module.Submodule.Basic

section Mathlib.Algebra.Module.Submodule.RestrictScalars

variable (S : Type _) {R M : Type _} [Mul R] [AddCommMonoid M] [Mul S]
  [SMul S M] [SMul R M]

def Submodule.restrictScalars (V : Submodule R M) : Submodule S M where
  carrier := V

end Mathlib.Algebra.Module.Submodule.RestrictScalars

section Mathlib.GroupTheory.QuotientGroup

universe u x

namespace QuotientAddGroup

variable {G : Type u} [AddGroup G] (N : AddSubgroup G) {M : Type x} [AddMonoid M]

protected def con : AddCon G where
  toSetoid := leftRel N

instance Quotient.addGroup : AddGroup (G ⧸ N) :=
  (QuotientAddGroup.con N).addGroup

instance Quotient.addCommGroup {G : Type _} [AddCommGroup G] (N : AddSubgroup G) : AddCommGroup (G ⧸ N) :=
  { toAddGroup := @QuotientAddGroup.Quotient.addGroup _ _ N }

def lift (φ : G →+ M) : G ⧸ N →+ M :=
  (QuotientAddGroup.con N).lift φ

end QuotientAddGroup

end Mathlib.GroupTheory.QuotientGroup

section Mathlib.Algebra.Algebra.Basic

universe u v

class Algebra (R : Type u) (A : Type v) [Mul R] [Mul A] extends SMul R A,
  R →* A where

end Mathlib.Algebra.Algebra.Basic

section Mathlib.Algebra.Module.LocalizedModule

namespace LocalizedModule

universe u v

variable {R : Type u} [MulOneClass R] (S : Submonoid R)
variable (M : Type v) [AddCommMonoid M] [SMul R M]

def r (a b : M × S) : Prop :=
  ∃ u : S, u • b.2 • a.1 = u • a.2 • b.1

instance r.setoid : Setoid (M × S) where
  r := r S M
  iseqv := sorry

def _root_.LocalizedModule : Type max u v :=
  Quotient (r.setoid S M)

section

variable {M S}

def mk (m : M) (s : S) : LocalizedModule S M :=
  Quotient.mk' ⟨m, s⟩

instance : AddCommMonoid (LocalizedModule S M) := sorry

noncomputable instance isModule' : SMul R (LocalizedModule S M) := sorry

end

end LocalizedModule

universe u v

variable {R : Type _} [MulOneClass R] (S : Submonoid R)
variable {M M' M'' : Type _} [AddCommMonoid M] [AddCommMonoid M']
variable [SMul R M] [SMul R M']
variable (f : M →ₗ[R] M')

class IsLocalizedModule (S : Submonoid R) (f : M →ₗ[R] M') : Prop where

namespace IsLocalizedModule

variable [IsLocalizedModule S f]

noncomputable def fromLocalizedModule (f : M →ₗ[R] M') [IsLocalizedModule S f] :
    LocalizedModule S M →ₗ[R] M' :=
  sorry

variable {S}

noncomputable def mk' (m : M) (s : S) : M' :=
  fromLocalizedModule S f (LocalizedModule.mk m s)

end IsLocalizedModule

end Mathlib.Algebra.Module.LocalizedModule

section Mathlib.LinearAlgebra.Quotient

namespace Submodule

variable {R M : Type _} {r : R} {x y : M} [Mul R] [AddCommGroup M] [SMul R M]
variable (p : Submodule R M)

open LinearMap

def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup

instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩

namespace Quotient

def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''

instance addCommGroup : AddCommGroup (M ⧸ p) :=
  QuotientAddGroup.Quotient.addCommGroup p.toAddSubgroup

section Module

variable {S : Type _}

instance module' [Mul S] [SMul S R] [SMul S M] (P : Submodule R M) :
    SMul S (M ⧸ P) := sorry

instance module (P : Submodule R M) : SMul R (M ⧸ P) :=
  Quotient.module' P

end Module

end Quotient

section

variable {M₂ : Type _} [AddCommGroup M₂] [SMul R M₂]

def mkQ : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk

end

variable {M₂ : Type _} [AddCommGroup M₂] [SMul R M₂]

def liftQ (f : M →ₗ[R] M₂) : M ⧸ p →ₗ[R] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom with }

variable (q : Submodule R M₂)

def mapQ (f : M →ₗ[R] M₂) : M ⧸ p →ₗ[R] M₂ ⧸ q :=
  p.liftQ (q.mkQ.comp f)

end Submodule

end Mathlib.LinearAlgebra.Quotient

section Mathlib.Algebra.Module.Submodule.Localization

universe u u' v v'

variable {R : Type u} (S : Type u') {M : Type v} {N : Type v'}
variable [MulOneClass R] [Mul S] [AddCommGroup M] [AddCommGroup N]
variable [SMul R M] [SMul R N] [Algebra R S] [SMul S N]
variable (p : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable (M' : Submodule R M)

/-- Let `S` be the localization of `R` at `p` and `N` be the localization of `M` at `p`.
This is the localization of an `R`-submodule of `M` viewed as an `S`-submodule of `N`. -/
def Submodule.localized' : Submodule S N where
  carrier := setOf fun x => ∃ m ∈ M', ∃ s : p, IsLocalizedModule.mk' f m s = x

/-- The localization map of a quotient module. -/
def Submodule.toLocalizedQuotient' : M ⧸ M' →ₗ[R] N ⧸ M'.localized' S p f :=
  Submodule.mapQ M' ((M'.localized' S p f).restrictScalars R) f

-- Should after `binrel%` and `binop%` were fixed
set_option maxHeartbeats 1000 in
theorem Submodule.toLocalizedQuotient'_mk₄ (x : M) :
    (M'.toLocalizedQuotient' S p f (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk (f x)) :=
  rfl

end Mathlib.Algebra.Module.Submodule.Localization
