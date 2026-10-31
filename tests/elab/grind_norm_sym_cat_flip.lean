module
@[expose] public section

/-!
`Functor.flip` from `grind_cat.lean` with the `Sym.simp`-based `grind` normalizer. The field
goals contain projections of structure instances in the implicit arguments of a composition,
e.g. `{ obj := fun j => (F.obj j).obj X, .. }.obj X₁` as an object of `≫`. `Sym.simp` does not
visit those arguments; without the `dsimp` pass after it, the beta-redex stays and the goal does
not match `NatTrans.naturality`.
-/
universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

section Mathlib.CategoryTheory.Category.Basic

class Category (obj : Type u) : Type max u (v + 1) where
  Hom : obj → obj → Type v
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (Hom X Y) → (Hom Y Z) → (Hom X Z)
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : Hom X Y), comp (id X) f = f := by grind
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : Hom X Y), comp f (id Y) = f := by grind
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), comp (comp f g) h = comp f (comp g h) := by grind

infixr:10 " ⟶ " => Category.Hom
scoped notation "𝟙" => Category.id  -- type as \b1
scoped infixr:80 " ≫ " => Category.comp

attribute [simp] Category.id_comp Category.comp_id Category.assoc

attribute [grind =] Category.id_comp Category.comp_id
attribute [grind _=_] Category.assoc

end Mathlib.CategoryTheory.Category.Basic

section Mathlib.CategoryTheory.Functor.Basic

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type max v₁ v₂ u₁ u₂ where
  /-- The action of a functor on objects. -/
  obj : C → D
  /-- The action of a functor on morphisms. -/
  map : ∀ {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y))
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by grind
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) := by grind

scoped infixr:26 " ⥤ " => Functor

attribute [simp] Functor.map_id Functor.map_comp

attribute [grind =] Functor.map_id
attribute [grind _=_] Functor.map_comp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable {F G H : Functor C D}

namespace Functor

def comp (F : Functor C D) (G : Functor D E) : Functor C E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  -- Note `map_id` and `map_comp` are handled by `grind`.

infixr:80 " ⋙ " => Functor.comp

variable {X Y : C} {G : Functor D E}

@[simp, grind =] theorem comp_obj : (F.comp G).obj X = G.obj (F.obj X) := rfl
@[simp, grind =] theorem comp_map (f : X ⟶ Y) : (F.comp G).map f = G.map (F.map f) := rfl

end Functor

end Mathlib.CategoryTheory.Functor.Basic

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
variable {F G H : Functor C D}

section Mathlib.CategoryTheory.NatTrans

@[ext]
structure NatTrans [Category.{v₁, u₁} C] [Category.{v₂, u₂} D] (F G : Functor C D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f := by grind

-- In the following examples `[grind ext] NatTrans.ext` is more effective than
-- `[grind ext] NatTrans` which only applies eta-extension because it will allows
-- chaining with function extensionality
attribute [grind ext] NatTrans.ext

attribute [simp, grind _=_] NatTrans.naturality

namespace NatTrans

variable {X : C}

protected def id (F : Functor C D) : NatTrans F F where app X := 𝟙 (F.obj X)

@[simp, grind =] theorem id_app' : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

protected def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  -- `naturality` is now handled by `grind`; in Mathlib this relies on `@[reassoc]` attributes.
  -- Manual proof:
  -- rw [← Category.assoc]
  -- rw [α.naturality f]
  -- rw [Category.assoc]
  -- rw [β.naturality f]
  -- rw [← Category.assoc]

@[simp, grind =] theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (α.vcomp β).app X = α.app X ≫ β.app X := rfl

end NatTrans

end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Functor.Category

instance Functor.category : Category.{max u₁ v₂} (Functor C D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := NatTrans.vcomp α β
  -- Here we're okay: all the proofs are handled by `grind`.

namespace NatTrans

@[ext, grind ext]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

@[simp, grind =]
theorem id_app (F : Functor C D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp, grind _=_]
theorem comp_app {F G H : Functor C D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

theorem app_naturality {F G : Functor C (Functor D E)} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
    (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f := by
  grind


end NatTrans

set_option backward.grind.normalizer false

namespace Functor

protected def flip (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E where
  obj k :=
    { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }

@[simp, grind =] theorem flip_obj_obj (F : C ⥤ D ⥤ E) (k : D) (j : C) : (F.flip.obj k).obj j = (F.obj j).obj k := rfl
@[simp, grind =] theorem flip_obj_map (F : C ⥤ D ⥤ E) (k : D) {j j' : C} (f : j ⟶ j') :
    (F.flip.obj k).map f = (F.map f).app k := rfl
@[simp, grind =] theorem flip_map_app (F : C ⥤ D ⥤ E) {k k' : D} (f : k ⟶ k') (j : C) :
    (F.flip.map f).app j = (F.obj j).map f := rfl

end Functor

end Mathlib.CategoryTheory.Functor.Category

end CategoryTheory
