universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

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

@[ext]
structure NatTrans [Category.{v₁, u₁} C] [Category.{v₂, u₂} D] (F G : Functor C D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f := by grind

attribute [simp, grind =] NatTrans.naturality

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

instance Functor.category : Category.{max u₁ v₂} (Functor C D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := NatTrans.vcomp α β
  -- Here we're okay: all the proofs are handled by `grind`.

namespace NatTrans

@[ext]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

@[simp, grind =]
theorem id_app (F : Functor C D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp, grind _=_]
theorem comp_app {F G H : Functor C D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

theorem app_naturality {F G : Functor C (Functor D E)} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
    (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f := by
  grind

theorem naturality_app {F G : Functor C (Functor D E)} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
    (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z := by
  grind -- this is done manually in Mathlib!
  -- rw [← comp_app]
  -- rw [T.naturality f]
  -- rw [comp_app]

open Category Functor NatTrans

def hcomp {H I : Functor D E} (α : F ⟶ G) (β : H ⟶ I) : F.comp H ⟶ G.comp I where
  app := fun X : C => β.app (F.obj X) ≫ I.map (α.app X)
  -- `grind` can now handle `naturality`, while Mathlib does this manually:
  -- rw [Functor.comp_map, Functor.comp_map, ← assoc, naturality, assoc, ← I.map_comp, naturality,
  --   map_comp, assoc]

/-- Notation for horizontal composition of natural transformations. -/
infixl:80 " ◫ " => hcomp

@[simp] theorem hcomp_app {H I : Functor D E} (α : F ⟶ G) (β : H ⟶ I) (X : C) :
    (α ◫ β).app X = β.app (F.obj X) ≫ I.map (α.app X) := rfl

attribute [grind =] hcomp_app

theorem hcomp_id_app {H : D ⥤ E} (α : F ⟶ G) (X : C) : (α ◫ 𝟙 H).app X = H.map (α.app X) := by
  grind

theorem id_hcomp_app {H : E ⥤ C} (α : F ⟶ G) (X : E) : (𝟙 H ◫ α).app X = α.app _ := by
  grind

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we
-- need to use associativity of functor composition. (It's true without the explicit associator,
-- because functor composition is definitionally associative,
-- but relying on the definitional equality causes bad problems with elaboration later.)
theorem exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ β ◫ δ := by
  ext X; grind

end NatTrans

structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X := by grind
  inv_hom_id : inv ≫ hom = 𝟙 Y := by grind

attribute [grind =] Iso.hom_inv_id Iso.inv_hom_id

/-- Notation for an isomorphism in a category. -/
infixr:10 " ≅ " => Iso -- type as \cong or \iso

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace Iso

@[ext]
theorem ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β :=
  suffices α.inv = β.inv by grind [Iso]
  calc
    α.inv = α.inv ≫ β.hom ≫ β.inv := by grind
    _     = β.inv                 := by grind


/-- `LeftInverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
def Function.LeftInverse (g : β → α) (f : α → β) : Prop :=
  ∀ x, g (f x) = x

/-- `RightInverse g f` means that g is a right inverse to f. That is, `f ∘ g = id`. -/
def Function.RightInverse (g : β → α) (f : α → β) : Prop :=
  LeftInverse f g

open Function

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α : Sort _) (β : Sort _) where
  protected toFun : α → β
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun
  protected right_inv : RightInverse invFun toFun

@[inherit_doc]
infixl:25 " ≃ " => Equiv

attribute [local grind] Function.LeftInverse in
/-- The bijection `(Z ⟶ X) ≃ (Z ⟶ Y)` induced by `α : X ≅ Y`. -/
def homToEquiv (α : X ≅ Y) {Z : C} : (Z ⟶ X) ≃ (Z ⟶ Y) where
  toFun f := f ≫ α.hom
  invFun g := g ≫ α.inv
  left_inv := by grind
  right_inv := sorry

end Iso

section Mathlib.CategoryTheory.Functor.Category


open NatTrans Category CategoryTheory.Functor

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

attribute [local simp] vcomp_app

variable {C D} {E : Type u₃} [Category.{v₃} E]
variable {E' : Type u₄} [Category.{v₄} E']
variable {F G H I : C ⥤ D}


namespace NatTrans

@[simp]
theorem vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.vcomp α β = α ≫ β := rfl

theorem vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X := rfl

theorem congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by grind

theorem naturality_app_app {F G : C ⥤ D ⥤ E ⥤ E'}
    (α : F ⟶ G) {X₁ Y₁ : C} (f : X₁ ⟶ Y₁) (X₂ : D) (X₃ : E) :
    ((F.map f).app X₂).app X₃ ≫ ((α.app Y₁).app X₂).app X₃ =
      ((α.app X₁).app X₂).app X₃ ≫ ((G.map f).app X₂).app X₃ := by
  grind

end NatTrans

open NatTrans

namespace Functor

/-- Flip the arguments of a bifunctor. See also `Currying.lean`. -/
protected def flip (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E where
  obj k :=
    { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }
  map_id k := by grind
  map_comp f g := sorry

@[simp] theorem flip_obj_obj (F : C ⥤ D ⥤ E) (k : D) : (F.flip.obj k).obj = fun j => (F.obj j).obj k := rfl
@[simp] theorem flip_obj_map (F : C ⥤ D ⥤ E) (k : D) {X Y : C}(f : X ⟶ Y) : (F.flip.obj k).map f = (F.map f).app k := rfl
@[simp] theorem flip_map_app (F : C ⥤ D ⥤ E) {X Y : D} (f : X ⟶ Y) (k : C) : (F.flip.map f).app k = (F.obj k).map f := rfl

attribute [grind =] flip_obj_obj flip_obj_map flip_map_app

end Functor

variable (C D E) in
/-- The functor `(C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E` which flips the variables. -/
def flipFunctor : (C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E where
  obj F := F.flip
  map {F₁ F₂} φ :=
    { app := fun Y =>
      { app := fun X => (φ.app X).app Y
        naturality := fun X₁ X₂ f => by grind
      }
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

namespace Iso

@[simp]
theorem map_hom_inv_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _ := by
  grind

@[simp]
theorem map_inv_hom_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _ := by
  grind

end Iso


end Mathlib.CategoryTheory.Functor.Category

end CategoryTheory
