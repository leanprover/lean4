set_option warn.classDefReducibility false

/-!
This is a minimization of a problem in Mathlib where a simp lemma `foo` would not fire,
but variants:
* `simp [(foo)]`
* `simp [foo.{v₁ + 1}]`
* `simp [foo']`, where a `no_index` is added in the statement
all work.
-/

section Mathlib.Data.Opposite

universe v u

variable (α : Sort u)

structure Opposite where
  op ::
  unop : α

notation:max α "ᵒᵖ" => Opposite α

end Mathlib.Data.Opposite

section Mathlib.Combinatorics.Quiver.Basic

open Opposite

universe v v₁ v₂ u u₁ u₂

class Quiver (V : Type u) where
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)
namespace Quiver

instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := ⟨f⟩

def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := Opposite.unop f

end Quiver


end Mathlib.Combinatorics.Quiver.Basic

section Mathlib.CategoryTheory.Category.Basic

universe v u

namespace CategoryTheory

class CategoryStruct (obj : Type u) : Type max u (v + 1) extends Quiver.{v + 1} obj where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

scoped notation "𝟙" => CategoryStruct.id

scoped infixr:80 " ≫ " => CategoryStruct.comp

class Category (obj : Type u) : Type max u (v + 1) extends CategoryStruct.{v} obj where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f

attribute [simp] Category.id_comp Category.comp_id

end CategoryTheory

end Mathlib.CategoryTheory.Category.Basic

section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type max v₁ v₂ u₁ u₂
    extends Prefunctor C D where

infixr:26 " ⥤ " => Functor

namespace Functor

section

variable (C : Type u₁) [Category.{v₁} C]

protected def id : C ⥤ C where
  obj X := X
  map f := f

notation "𝟭" => Functor.id

variable {C}

@[simp]
theorem id_obj (X : C) : (𝟭 C).obj X = X := rfl

end

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

@[simp]
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

infixr:80 " ⋙ " => Functor.comp

end Functor

end CategoryTheory


end Mathlib.CategoryTheory.Functor.Basic

section Mathlib.CategoryTheory.NatTrans

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  app : ∀ X : C, F.obj X ⟶ G.obj X

end CategoryTheory

end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Iso

universe v u

namespace CategoryTheory

open Category

structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X

infixr:10 " ≅ " => Iso

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace Iso

@[simp]
def symm (I : X ≅ Y) : Y ≅ X where
  hom := I.inv
  inv := I.hom

@[simp]
def refl (X : C) : X ≅ X where
  hom := 𝟙 X
  inv := 𝟙 X

@[simp]
def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where
  hom := α.hom ≫ β.hom
  inv := β.inv ≫ α.inv

infixr:80 " ≪≫ " => Iso.trans

end Iso

namespace Functor

universe u₂ v₂

variable {D : Type u₂} [Category.{v₂} D]

@[simp]
def mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  hom := F.map i.hom
  inv := F.map i.inv

end Functor

end CategoryTheory


end Mathlib.CategoryTheory.Iso

section Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := sorry
  comp α β := sorry
  id_comp := sorry
  comp_id := sorry

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Category

section Mathlib.CategoryTheory.NatIso


open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Iso

@[simp]
def app {F G : C ⥤ D} (α : F ≅ G) (X : C) : F.obj X ≅ G.obj X where
  hom := α.hom.app X
  inv := α.inv.app X

end Iso

namespace NatIso

variable {F G : C ⥤ D} {X : C}

@[simp]
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X) :
    F ≅ G where
  hom :=
  { app := fun X => (app X).hom }
  inv :=
    { app := fun X => (app X).inv }

end NatIso


end CategoryTheory


end Mathlib.CategoryTheory.NatIso

section Mathlib.CategoryTheory.Equivalence

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

universe v₁ v₂ v₃ u₁ u₂ u₃

structure Equivalence (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] where mk' ::
  functor : C ⥤ D
  inverse : D ⥤ C
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  counitIso : inverse ⋙ functor ≅ 𝟭 D

infixr:10 " ≌ " => Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

@[simp]
def Equivalence.symm (e : C ≌ D) : D ≌ C :=
  ⟨e.inverse, e.functor, e.counitIso.symm, e.unitIso.symm⟩

end CategoryTheory


end Mathlib.CategoryTheory.Equivalence

section Mathlib.CategoryTheory.Opposites

universe v₁ v₂ u₁ u₂

open Opposite

variable {C : Type u₁}

@[simp]
theorem Quiver.Hom.unop_op [Quiver.{v₁} C] {X Y : C} (f : X ⟶ Y) : f.op.unop = f :=
  rfl

namespace CategoryTheory

variable [Category.{v₁} C]

instance Category.opposite : Category.{v₁} Cᵒᵖ where
  comp f g := (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op
  id_comp := sorry
  comp_id := sorry

protected def Iso.op {X Y : C} (α : X ≅ Y) : op Y ≅ op X where
  hom := α.hom.op
  inv := α.inv.op

end CategoryTheory


end Mathlib.CategoryTheory.Opposites

section Mathlib.CategoryTheory.Monoidal.Category

universe v u

namespace CategoryTheory

class MonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  tensorObj : C → C → C
  whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : tensorObj X Y₁ ⟶ tensorObj X Y₂
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : tensorObj X₁ Y ⟶ tensorObj X₂ Y
  tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerRight f X₂ ≫ whiskerLeft Y₁ g
  tensorUnit : C
  rightUnitor : ∀ X : C, tensorObj X tensorUnit ≅ X

namespace MonoidalCategory

scoped infixr:70 " ⊗ " => MonoidalCategoryStruct.tensorObj
scoped infixr:81 " ◁ " => MonoidalCategoryStruct.whiskerLeft
scoped infixl:81 " ▷ " => MonoidalCategoryStruct.whiskerRight
scoped infixr:70 " ⊗ " => MonoidalCategoryStruct.tensorHom
scoped notation "𝟙_ " C:max => (MonoidalCategoryStruct.tensorUnit : C)
scoped notation "ρ_" => MonoidalCategoryStruct.rightUnitor

end MonoidalCategory

open MonoidalCategory

class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends MonoidalCategoryStruct C where
  id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)

attribute [simp] MonoidalCategory.id_whiskerRight

namespace MonoidalCategory

variable {C : Type u} [𝒞 : Category.{v} C] [MonoidalCategory C]

@[simp]
theorem id_tensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⊗ f = X ◁ f := sorry

@[simp]
theorem tensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ⊗ 𝟙 Y = f ▷ Y := sorry

end MonoidalCategory

@[simp]
def tensorIso {C : Type u} {X Y X' Y' : C} [Category.{v} C] [MonoidalCategory.{v} C] (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ g.hom
  inv := f.inv ⊗ g.inv

infixr:70 " ⊗ " => tensorIso

end CategoryTheory

end Mathlib.CategoryTheory.Monoidal.Category

section Mathlib.CategoryTheory.Monoidal.Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

open Opposite MonoidalCategory

instance monoidalCategoryOp : MonoidalCategory Cᵒᵖ where
  tensorObj X Y := op (unop X ⊗ unop Y)
  whiskerLeft X _ _ f := (X.unop ◁ f.unop).op
  whiskerRight f X := (f.unop ▷ X.unop).op
  tensorHom f g := (f.unop ⊗ g.unop).op
  tensorUnit := op (𝟙_ C)
  id_whiskerRight := sorry
  rightUnitor X := (ρ_ (unop X)).symm.op


@[simp] theorem op_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (X ◁ f).op = op X ◁ f.op := rfl
@[simp] theorem unop_whiskerLeft (X : Cᵒᵖ) {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    (X ◁ f).unop =  unop X ◁ f.unop := rfl

@[simp] theorem op_hom_rightUnitor (X : C) : (ρ_ X).hom.op = (ρ_ (op X)).inv := rfl
@[simp] theorem unop_hom_rightUnitor (X : Cᵒᵖ) : (ρ_ X).hom.unop = (ρ_ (unop X)).inv := rfl

@[simp] theorem op_inv_rightUnitor (X : C) : (ρ_ X).inv.op = (ρ_ (op X)).hom := rfl
@[simp] theorem unop_inv_rightUnitor (X : Cᵒᵖ) : (ρ_ X).inv.unop = (ρ_ (unop X)).hom := rfl

end CategoryTheory


end Mathlib.CategoryTheory.Monoidal.Opposite

section Mathlib.CategoryTheory.Monoidal.Transport

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

abbrev induced [MonoidalCategoryStruct D] (F : D ⥤ C) :
    MonoidalCategory.{v₂} D where
  id_whiskerRight X Y := sorry

def transportStruct (e : C ≌ D) : MonoidalCategoryStruct.{v₂} D where
  tensorObj X Y := e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)
  whiskerLeft X _ _ f := e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
  whiskerRight f X := sorry
  tensorHom f g := sorry
  tensorUnit := e.functor.obj (𝟙_ C)
  rightUnitor X :=
    e.functor.mapIso ((Iso.refl _ ⊗ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _

@[simp] theorem transportStruct_whiskerLeft (e : C ≌ D) (X x x_1 : D) (f : x ⟶ x_1) :
  (transportStruct e).whiskerLeft X f = e.functor.map (e.inverse.obj X ◁ e.inverse.map f) := rfl

@[simp] theorem transportStruct_rightUnitor (e : C ≌ D) (X : D) :
  (transportStruct e).rightUnitor X =
    e.functor.mapIso ((Iso.refl _ ⊗ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _ := rfl

def transport (e : C ≌ D) : MonoidalCategory.{v₂} D :=
  letI : MonoidalCategoryStruct.{v₂} D := transportStruct e
  induced e.inverse

end CategoryTheory.Monoidal

end

end Mathlib.CategoryTheory.Monoidal.Transport

section Mathlib.CategoryTheory.Monoidal.Braided.Basic

open CategoryTheory MonoidalCategory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

def tensor_μ (X Y : C × C) : (X.1 ⊗ X.2) ⊗ Y.1 ⊗ Y.2 ⟶ (X.1 ⊗ Y.1) ⊗ X.2 ⊗ Y.2 :=
  sorry

end CategoryTheory

end Mathlib.CategoryTheory.Monoidal.Braided.Basic

section Mathlib.CategoryTheory.Monoidal.Mon_

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

structure Mon_ where
  X : C
  one : 𝟙_ C ⟶ X
  mul : X ⊗ X ⟶ X
  mul_one : (X ◁ one) ≫ mul = (ρ_ X).hom

attribute [simp] Mon_.mul_one
namespace Mon_

@[simp]
def trivial : Mon_ C where
  X := 𝟙_ C
  one := 𝟙 _
  mul := sorry
  mul_one := sorry

variable {C}
variable {M : Mon_ C}

structure Hom (M N : Mon_ C) where
  hom : M.X ⟶ N.X

@[simp]
def id (M : Mon_ C) : Hom M M where
  hom := 𝟙 M.X

@[simp]
def comp {M N O : Mon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Mon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g
  id_comp := sorry
  comp_id := sorry

@[ext]
theorem ext {X Y : Mon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := sorry

@[simp]
theorem id_hom' (M : Mon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := sorry

@[simp]
theorem comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom := sorry

variable (C) in
@[simp]
def forget : Mon_ C ⥤ C where
  obj A := A.X
  map f := f.hom

@[simp]
def isoOfIso {M N : Mon_ C} (f : M.X ≅ N.X) : M ≅ N where
  hom := { hom := f.hom }
  inv := { hom := f.inv }

@[simp]
instance monMonoidalStruct : MonoidalCategoryStruct (Mon_ C) :=
  let tensorObj (M N : Mon_ C) : Mon_ C :=
    { X := M.X ⊗ N.X
      one := sorry
      mul := tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)
      mul_one := sorry }
  let tensorHom {X₁ Y₁ X₂ Y₂ : Mon_ C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
      tensorObj _ _ ⟶ tensorObj _ _ :=
    { hom := f.hom ⊗ g.hom }
  { tensorObj := tensorObj
    tensorHom := tensorHom
    whiskerRight := fun f Y => tensorHom f (𝟙 Y)
    whiskerLeft := fun X _ _ g => tensorHom (𝟙 X) g
    tensorUnit := trivial C
    rightUnitor := fun M ↦ isoOfIso (ρ_ M.X) }

@[simp]
theorem whiskerLeft_hom {X Y : Mon_ C} (f : X ⟶ Y) (Z : Mon_ C) :
    (f ▷ Z).hom = f.hom ▷ Z.X := by
  rw [← tensorHom_id]; rfl

@[simp]
theorem whiskerRight_hom (X : Mon_ C) {Y Z : Mon_ C} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.X ◁ f.hom := by
  rw [← id_tensorHom]; rfl

@[simp]
theorem rightUnitor_inv_hom (X : Mon_ C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

instance monMonoidal : MonoidalCategory (Mon_ C) where
  id_whiskerRight := sorry

end Mon_

end Mathlib.CategoryTheory.Monoidal.Mon_

section Mathlib.CategoryTheory.Monoidal.Comon_

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

structure Comon_ where
  X : C
  counit : X ⟶ 𝟙_ C
  comul : X ⟶ X ⊗ X

namespace Comon_

variable {C}
variable {M : Comon_ C}

structure Hom (M N : Comon_ C) where
  hom : M.X ⟶ N.X

@[simp]
def id (M : Comon_ C) : Hom M M where
  hom := 𝟙 M.X

@[simp]
def comp {M N O : Comon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Comon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g
  comp_id := sorry
  id_comp := sorry

@[ext] theorem ext {X Y : Comon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := sorry

@[simp] theorem id_hom' (M : Comon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Comon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

open Opposite

variable (C)

def Comon_to_Mon_op_op_obj' (A : Comon_ C) : Mon_ (Cᵒᵖ) where
  X := op A.X
  one := A.counit.op
  mul := A.comul.op
  mul_one := sorry

@[simp] theorem Comon_to_Mon_op_op_obj'_X (A : Comon_ C) : (Comon_to_Mon_op_op_obj' C A).X = op A.X := rfl

@[simp] def Comon_to_Mon_op_op : Comon_ C ⥤ (Mon_ (Cᵒᵖ))ᵒᵖ where
  obj A := op (Comon_to_Mon_op_op_obj' C A)
  map := fun f => op <| { hom := f.hom.op }

def Mon_op_op_to_Comon_obj' (A : (Mon_ (Cᵒᵖ))) : Comon_ C where
  X := unop A.X
  counit := A.one.unop
  comul := A.mul.unop

@[simp] theorem Mon_op_op_to_Comon_obj'_X (A : (Mon_ (Cᵒᵖ))) : (Mon_op_op_to_Comon_obj' C A).X = unop A.X := rfl

@[simp]
def Mon_op_op_to_Comon : (Mon_ (Cᵒᵖ))ᵒᵖ ⥤ Comon_ C where
  obj A := Mon_op_op_to_Comon_obj' C (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop }

@[simp]
def Comon_equiv_Mon_op_op : Comon_ C ≌ (Mon_ (Cᵒᵖ))ᵒᵖ :=
  { functor := Comon_to_Mon_op_op C
    inverse := Mon_op_op_to_Comon C
    unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    counitIso := NatIso.ofComponents (fun _ => Iso.refl _) }

instance : MonoidalCategory (Comon_ C) :=
  Monoidal.transport (Comon_equiv_Mon_op_op C).symm

end Comon_

namespace CategoryTheory.Functor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

def mapComon (F : C ⥤ D) : Comon_ C ⥤ Comon_ D where
  obj A :=
    { X := F.obj A.X
      counit := sorry
      comul := sorry }
  map f := sorry

end CategoryTheory.Functor


end Mathlib.CategoryTheory.Monoidal.Comon_

section Mathlib.CategoryTheory.Monoidal.Bimon_

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

def toComon_ : Comon_ (Mon_ C) ⥤ Comon_ C := (Mon_.forget C).mapComon

@[simp] theorem toComon_obj_X (M : Comon_ (Mon_ C)) : ((toComon_ C).obj M).X = M.X.X := rfl

theorem foo {V} [Quiver V] {X Y x} :
    @Quiver.Hom.unop V _ X Y (Opposite.op (unop := x)) = x := rfl

set_option backward.isDefEq.respectTransparency false in
example (M : Comon_ (Mon_ C)) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := M.X.one }
  mul := { hom := M.X.mul }
  mul_one := by
    ext
    simp [(foo)] -- parentheses around `foo` works

set_option backward.isDefEq.respectTransparency false in
example (M : Comon_ (Mon_ C)) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := M.X.one }
  mul := { hom := M.X.mul }
  mul_one := by
    ext
    simp [foo.{_, v₁ + 1}] -- specifying the universe level explicitly works!

theorem foo' {V} [Quiver V] {X Y x} :
    @Quiver.Hom.unop V _ X Y no_index (Opposite.op (unop := x)) = x := rfl

set_option backward.isDefEq.respectTransparency false in
example (M : Comon_ (Mon_ C)) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := M.X.one }
  mul := { hom := M.X.mul }
  mul_one := by
    ext
    simp [foo'] -- or adding a `no_index` in the statement


set_option backward.isDefEq.respectTransparency false in
/--
trace: [simp] Diagnostics
  [simp] theorems with bad keys
    [simp] foo, key: @Quiver.Hom.unop _ _ _ _ (@Opposite.op (@Quiver.Hom _ _ _.1 _.1) _)
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example (M : Comon_ (Mon_ C)) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := M.X.one }
  mul := { hom := M.X.mul, }
  mul_one := by
    ext
    -- increase the threshold to ensure the guard_msgs docstring is not too big.
    set_option diagnostics.threshold 100000 in
    set_option diagnostics true in
    -- `index := false` ignores most of the discrimination tree structure.
    simp (config := { index := false }) [foo]

attribute [simp] foo

set_option backward.isDefEq.respectTransparency false in
/--
trace: [simp] Diagnostics
  [simp] theorems with bad keys
    [simp] foo, key: @Quiver.Hom.unop _ _ _ _ (@Opposite.op (@Quiver.Hom _ _ _.1 _.1) _)
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example (M : Comon_ (Mon_ C)) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := M.X.one }
  mul := { hom := M.X.mul, }
  mul_one := by
    ext
    -- increase the threshold to ensure the guard_msgs docstring is not too big.
    set_option diagnostics.threshold 100000 in
    set_option diagnostics true in
    -- `index := false` ignores most of the discrimination tree structure.
    simp (config := { index := false })

end

end Mathlib.CategoryTheory.Monoidal.Bimon_
