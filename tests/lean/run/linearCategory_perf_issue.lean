universe u v w v₁ v₂ v₃ u₁ u₂ u₃

section Mathlib.Algebra.Group.Defs

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

class SMul (M : Type u) (α : Type v) where
  smul : M → α → α

infixr:73 " • " => SMul.smul

macro_rules | `($x • $y) => `(leftact% HSMul.hSMul $x $y)

instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

class AddMonoid (M : Type u) extends Add M, Zero M where
  protected add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a

section AddMonoid
variable {M : Type u} [AddMonoid M] {a b c : M}

theorem add_assoc : ∀ a b c : M, a + b + c = a + (b + c) :=
  AddMonoid.add_assoc

theorem zero_add : ∀ a : M, 0 + a = a :=
  AddMonoid.zero_add

theorem add_zero : ∀ a : M, a + 0 = a :=
  AddMonoid.add_zero

theorem left_neg_eq_right_neg (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  rw [← zero_add c, ← hba, add_assoc, hac, add_zero b]

end AddMonoid

class AddGroup (A : Type u) extends AddMonoid A, Neg A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0

section Group

variable {G : Type u} [AddGroup G] {a b c : G}

theorem neg_add_cancel (a : G) : -a + a = 0 :=
  AddGroup.neg_add_cancel a

theorem neg_eq_of_add (h : a + b = 0) : -a = b :=
  left_neg_eq_right_neg (neg_add_cancel a) h

theorem add_neg_cancel (a : G) : a + -a = 0 := by
  rw [← neg_add_cancel (-a), neg_eq_of_add (neg_add_cancel a)]

theorem add_neg_cancel_right (a b : G) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

theorem neg_neg (a : G) : - -a = a :=
  neg_eq_of_add (neg_add_cancel a)

theorem neg_eq_of_add_eq_zero_left (h : a + b = 0) : -b = a := by
  rw [← neg_eq_of_add h, neg_neg]

theorem eq_neg_of_add_eq_zero_left (h : a + b = 0) : a = -b :=
  (neg_eq_of_add_eq_zero_left h).symm

theorem add_right_cancel (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

end Group

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.Group.Hom.Defs

structure AddMonoidHom (M : Type u) (N : Type v) [AddMonoid M] [AddMonoid N] where
  toFun : M → N
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

infixr:25 " →+ " => AddMonoidHom

namespace AddMonoidHom

variable {M : Type u} {N : Type v}

instance [AddMonoid M] [AddMonoid N] : CoeFun (M →+ N) (fun _ => M → N) where
  coe := toFun

section

variable [AddMonoid M] [AddGroup N]

def mk' (f : M → N) (map_add : ∀ a b : M, f (a + b) = f a + f b) : M →+ N where
  toFun := f
  map_add' := map_add

end

section

variable [AddGroup M] [AddGroup N]

theorem map_zero (f : M →+ N) : f 0 = 0 := by
  have := calc f 0 + f 0
            = f (0 + 0) := by rw [f.map_add']
          _ = 0 + f 0 := by rw [zero_add, zero_add]
  exact add_right_cancel this

theorem map_neg (f : M →+ N) (m : M) : f (-m) = - (f m) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← f.map_add']
  simp only [neg_add_cancel, f.map_zero]

end

end AddMonoidHom

end Mathlib.Algebra.Group.Hom.Defs

section Mathlib.Algebra.Group.Action.Defs

class MulOneClass (M : Type u) extends Mul M, One M where

class MulAction (α : Type u) (β : Type v) [MulOneClass α] extends SMul α β where
  protected one_smul : ∀ b : β, (1 : α) • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

end Mathlib.Algebra.Group.Action.Defs

section Mathlib.Algebra.GroupWithZero.Action.Defs

class DistribMulAction (M : Type u) (A : Type v) [MulOneClass M] [AddMonoid A] extends MulAction M A where
  smul_zero : ∀ a : M, a • (0 : A) = 0
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

export DistribMulAction (smul_zero smul_add)

end Mathlib.Algebra.GroupWithZero.Action.Defs

section Mathlib.Algebra.Ring.Defs

class Semiring (α : Type u) extends AddMonoid α, MulOneClass α where

end Mathlib.Algebra.Ring.Defs

section Mathlib.Algebra.Module.Defs

class Module (R : Type u) (M : Type v) [Semiring R] [AddMonoid M] extends
  DistribMulAction R M where
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

export Module (add_smul zero_smul)

end Mathlib.Algebra.Module.Defs

section Mathlib.Combinatorics.Quiver.Basic

class Quiver (V : Type u₁) where
  Hom : V → V → Sort v₁

infixr:10 " ⟶ " => Quiver.Hom

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

end Mathlib.Combinatorics.Quiver.Basic

section Mathlib.CategoryTheory.Category.Basic

namespace CategoryTheory

class CategoryStruct (obj : Type u₁) : Type max u₁ (v₁ + 1) extends Quiver.{v₁ + 1} obj where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

scoped notation "𝟙" => CategoryStruct.id  -- type as \b1
scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

class Category (obj : Type u₁) : Type max u₁ (v₁ + 1) extends CategoryStruct.{v₁} obj where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h

end CategoryTheory

end Mathlib.CategoryTheory.Category.Basic

section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type max v₁ v₂ u₁ u₂
    extends Prefunctor C D where

infixr:26 " ⥤ " => Functor -- type as \func

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Basic

section Mathlib.CategoryTheory.NatTrans

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

@[ext (iff := false)]
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

theorem NatTrans.naturality_assoc {F G : C ⥤ D} (self : NatTrans F G) ⦃X Y : C⦄ (f : X ⟶ Y) {Z : D}
    (h : G.obj Y ⟶ Z) : F.map f ≫ self.app Y ≫ h = self.app X ≫ G.map f ≫ h := by
  rw [← Category.assoc, NatTrans.naturality, Category.assoc]

namespace NatTrans

protected def id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := by
    intro X Y f
    simp_all only [Category.comp_id, Category.id_comp]

open Category

variable {F G H : C ⥤ D}

def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := by
    intro X Y f
    simp_all only [naturality_assoc, naturality, assoc]

end NatTrans

end CategoryTheory

end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory

open NatTrans Category

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β
  id_comp := by
    intro X Y f
    ext x : 2
    apply id_comp
  comp_id := by
    intro X Y f
    ext x : 2
    apply comp_id
  assoc := by
    intro W X Y Z f g h
    ext x : 2
    apply assoc

namespace NatTrans

@[ext (iff := false)]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

end NatTrans

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Category

section Mathlib.CategoryTheory.Preadditive.Basic

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

class Preadditive where
  homGroup : ∀ P Q : C, AddGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'

attribute [instance] Preadditive.homGroup

end CategoryTheory

namespace CategoryTheory

namespace Preadditive

open AddMonoidHom

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp only [comp_add]

def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  mk' (fun f => f ≫ g) fun f f' => by simp only [add_comp]

variable {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R)

theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f

theorem comp_neg : f ≫ (-g) = -f ≫ g :=
  map_neg (leftComp R f) g

theorem comp_zero : f ≫ (0 : Q ⟶ R) = 0 :=
  show leftComp R f 0 = 0 from map_zero _

theorem zero_comp : (0 : P ⟶ Q) ≫ g = 0 :=
  show rightComp P g 0 = 0 from map_zero _

end Preadditive

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Preadditive.Basic

namespace CategoryTheory

open Preadditive

variable {C : Type u₁} {D : Type u₂} [Category C] [Category D] [Preadditive D]

instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero :=
   { app := fun X => 0
     naturality := by
       intro X Y f
       rw [Preadditive.comp_zero, Preadditive.zero_comp] }

instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β :=
  { app := fun X => α.app X + β.app X,
    naturality := by
      intro X Y f
      simp_all only [comp_add, NatTrans.naturality, add_comp] }

instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α :=
  { app := fun X => -α.app X,
    naturality := by
      intro X Y f
      simp_all only [comp_neg, NatTrans.naturality, neg_comp] }

instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { add_assoc := by
        intros
        ext
        apply add_assoc
      zero_add := by
        intros
        ext
        apply zero_add
      add_zero := by
        intros
        ext
        apply add_zero
      neg_add_cancel := by
        intros
        ext
        apply neg_add_cancel }
  add_comp := by
    intros
    dsimp only [id_eq]
    ext
    apply add_comp
  comp_add := by
    intros
    dsimp only [id_eq]
    ext
    apply comp_add

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Linear.Basic

namespace CategoryTheory

class Linear (R : Type w) [Semiring R] (C : Type u₁) [Category.{v₁} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g

attribute [instance] Linear.homModule

end CategoryTheory

end Mathlib.CategoryTheory.Linear.Basic

namespace CategoryTheory

variable {R : Type w} [Semiring R]
variable {C : Type u₁} {D : Type u₂} [Category C] [Category D] [Preadditive D] [Linear R D]

set_option maxHeartbeats 10000 in
instance functorCategoryLinear : Linear R (C ⥤ D) where
  homModule F G :=
    {
      smul := fun r α ↦
        { app := fun X ↦ r • α.app X
          naturality := by
            intros
            rw [Linear.comp_smul, Linear.smul_comp, α.naturality] }
      one_smul := by
        intros
        ext
        apply MulAction.one_smul
      zero_smul := by
        intros
        ext
        apply Module.zero_smul
      smul_zero := by
        intros
        ext
        apply DistribMulAction.smul_zero
      add_smul := by
        intros
        ext
        apply Module.add_smul
      smul_add := by
        intros
        ext
        apply DistribMulAction.smul_add
      mul_smul := by
        intros
        ext
        apply MulAction.mul_smul
        }
  smul_comp := by
    intros
    ext
    apply Linear.smul_comp
  comp_smul := by
    intros
    ext
    apply Linear.comp_smul

end CategoryTheory
