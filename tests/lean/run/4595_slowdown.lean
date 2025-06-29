-- The final declaration blew up by a factor of about 40x heartbeats on an earlier draft of
-- https://github.com/leanprover/lean4/pull/4595, so this is here as a regression test.

universe v v₁ v₂ v₃ u u₁ u₂ u₃

section Mathlib.Combinatorics.Quiver.Basic

class Quiver (V : Type u) where
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

end Mathlib.Combinatorics.Quiver.Basic

section Mathlib.CategoryTheory.Category.Basic

namespace CategoryTheory

class CategoryStruct (obj : Type u) : Type max u (v + 1) extends Quiver.{v + 1} obj where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

scoped notation "𝟙" => CategoryStruct.id

scoped infixr:80 " ≫ " => CategoryStruct.comp

class Category (obj : Type u) : Type max u (v + 1) extends CategoryStruct.{v} obj where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f

end CategoryTheory

end Mathlib.CategoryTheory.Category.Basic

section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

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

@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl

end

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

infixr:80 " ⋙ " => Functor.comp

@[simp] theorem comp_obj (F : C ⥤ D) (G : D ⥤ E) (X : C) :
  (F ⋙ G).obj X = G.obj (F.obj X) := rfl

@[simp]
theorem comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := rfl

end Functor

end CategoryTheory


end Mathlib.CategoryTheory.Functor.Basic

section Mathlib.CategoryTheory.NatTrans

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

@[ext]
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

protected def NatTrans.id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := sorry

end CategoryTheory

end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Iso

namespace CategoryTheory

structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X
  inv_hom_id : inv ≫ hom = 𝟙 Y

infixr:10 " ≅ " => Iso

end CategoryTheory

end Mathlib.CategoryTheory.Iso

section Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

namespace Functor

instance category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := sorry
  id_comp := sorry
  comp_id := sorry

@[ext]
theorem ext' {F G : C ⥤ D} {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

end Functor

namespace NatTrans

@[simp]
theorem id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp]
theorem comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := sorry

end NatTrans

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Category

section Mathlib.CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

variable (C : Type _) [Category C]

structure Karoubi where
  X : C
  p : X ⟶ X

namespace Karoubi

variable {C}

structure Hom (P Q : Karoubi C) where
  f : P.X ⟶ Q.X
  comm : f = P.p ≫ f ≫ Q.p

theorem p_comp {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f := sorry

theorem comp_p {P Q : Karoubi C} (f : Hom P Q) : f.f ≫ Q.p = f.f := sorry

/-- The category structure on the karoubi envelope of a category. -/
instance : Category (Karoubi C) where
  Hom := Karoubi.Hom
  id P := ⟨P.p, sorry⟩
  comp f g := ⟨f.f ≫ g.f, sorry⟩
  comp_id := sorry
  id_comp := sorry

@[simp]
theorem hom_ext_iff {P Q : Karoubi C} {f g : P ⟶ Q} : f = g ↔ f.f = g.f := sorry

@[ext]
theorem hom_ext {P Q : Karoubi C} (f g : P ⟶ Q) (h : f.f = g.f) : f = g := sorry

@[simp]
theorem comp_f {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).f = f.f ≫ g.f := rfl

@[simp]
theorem id_f {P : Karoubi C} : Hom.f (𝟙 P) = P.p := rfl

end Karoubi

def toKaroubi : C ⥤ Karoubi C where
  obj X := ⟨X, 𝟙 X⟩
  map f := ⟨f, sorry⟩

@[simp] theorem toKaroubi_obj_X (X : C) : ((toKaroubi C).obj X).X = X := rfl
@[simp] theorem toKaroubi_obj_p (X : C) : ((toKaroubi C).obj X).p = 𝟙 X := rfl
@[simp] theorem toKaroubi_map_f {X Y : C} (f : X ⟶ Y) : ((toKaroubi C).map f).f = f := rfl

end CategoryTheory

end Mathlib.CategoryTheory.Idempotents.Karoubi

section Mathlib.CategoryTheory.Idempotents.KaroubiKaroubi

open CategoryTheory.Category
open CategoryTheory.Karoubi

namespace CategoryTheory
namespace Idempotents

variable (C : Type _) [Category C]

theorem idem_f (P : Karoubi (Karoubi C)) : P.p.f ≫ P.p.f = P.p.f := sorry

theorem p_comm_f {P Q : Karoubi (Karoubi C)} (f : P ⟶ Q) : P.p.f ≫ f.f.f = f.f.f ≫ Q.p.f := sorry

def inverse : Karoubi (Karoubi C) ⥤ Karoubi C where
  obj P := ⟨P.X.X, P.p.f⟩
  map f := ⟨f.f.f, sorry⟩

theorem inverse_obj_X (P : Karoubi (Karoubi C)) : ((inverse C).obj P).X = P.X.X := rfl
theorem inverse_obj_p (P : Karoubi (Karoubi C)) : ((inverse C).obj P).p = P.p.f := rfl
theorem inverse_map_f {X Y : Karoubi (Karoubi C)} (f : X ⟶ Y) : ((inverse C).map f).f = f.f.f := rfl

-- In the original source this is just
-- ```
-- def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
--   hom := { app := fun P => { f := { f := P.p.1 } } }
--   inv := { app := fun P => { f := { f := P.p.1 }  } }
-- ```
-- but I've maximally expanded out the autoparams:
-- it seems the slow down is in the `simp only` tactics, not the automation that finds them.

def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
  hom :=
    { app := fun P =>
        { f :=
            { f := P.p.1
              comm := by simp only [Functor.comp_obj, toKaroubi_obj_X, inverse_obj_X,
                Functor.id_obj, inverse_obj_p, comp_p, idem_f] }
          comm := by simp only [Functor.comp_obj, toKaroubi_obj_X, Functor.id_obj, toKaroubi_obj_p,
            Karoubi.id_f, inverse_obj_p, hom_ext_iff, inverse_obj_X, comp_f, idem_f] }
      naturality := by
        intro X Y f
        simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, toKaroubi_obj_X,
          Functor.id_map, hom_ext_iff, comp_f, toKaroubi_map_f, inverse_obj_X, inverse_map_f,
          p_comm_f] }
  inv :=
    { app := fun P =>
        { f :=
            { f := P.p.1
              comm := by simp only [Functor.id_obj, Functor.comp_obj, toKaroubi_obj_X,
                inverse_obj_X, inverse_obj_p, idem_f, p_comp] }
          comm := by simp only [Functor.id_obj, Functor.comp_obj, toKaroubi_obj_X, toKaroubi_obj_p,
            Karoubi.id_f, inverse_obj_p, hom_ext_iff, inverse_obj_X, comp_f, idem_f] }
      naturality := by
        intro X Y f
        simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, toKaroubi_obj_X,
          Functor.comp_map, hom_ext_iff, comp_f, toKaroubi_map_f, inverse_obj_X, inverse_map_f,
          p_comm_f]
    }
  hom_inv_id := by
    simp only [Functor.comp_obj, Functor.id_obj, toKaroubi_obj_X]
    ext x : 4
    simp only [Functor.comp_obj, toKaroubi_obj_X, inverse_obj_X, NatTrans.comp_app,
      Functor.id_obj, comp_f, idem_f, NatTrans.id_app, Karoubi.id_f, toKaroubi_obj_p,
      inverse_obj_p]
  inv_hom_id := by
    simp only [Functor.id_obj, Functor.comp_obj, toKaroubi_obj_X]
    ext x : 4
    simp only [Functor.id_obj, NatTrans.comp_app, Functor.comp_obj, comp_f, toKaroubi_obj_X,
      inverse_obj_X, idem_f, NatTrans.id_app, Karoubi.id_f]
