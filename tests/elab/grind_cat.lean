module
@[expose] public section
set_option backward.defeqAttrib.useBackward true
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

section Mathlib.CategoryTheory.Iso

structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X := by grind
  inv_hom_id : inv ≫ hom = 𝟙 Y := by grind

attribute [simp, grind =] Iso.hom_inv_id Iso.inv_hom_id

/-- Notation for an isomorphism in a category. -/
infixr:10 " ≅ " => Iso -- type as \cong or \iso

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace Iso

@[ext, grind ext]
theorem ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β :=
  suffices α.inv = β.inv by grind [Iso]
  calc
    α.inv = α.inv ≫ β.hom ≫ β.inv := by grind
    _     = β.inv                 := by grind

/-- Inverse isomorphism. -/
@[symm]
def symm (I : X ≅ Y) : Y ≅ X where
  hom := I.inv
  inv := I.hom

@[simp, grind =]
theorem symm_hom (α : X ≅ Y) : α.symm.hom = α.inv :=
  rfl

@[simp, grind =]
theorem symm_inv (α : X ≅ Y) : α.symm.inv = α.hom :=
  rfl

@[simp, grind =]
theorem symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) :
    Iso.symm { hom, inv, hom_inv_id := hom_inv_id, inv_hom_id := inv_hom_id } =
      { hom := inv, inv := hom, hom_inv_id := inv_hom_id, inv_hom_id := hom_inv_id } :=
  rfl

@[simp, grind =]
theorem symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α := rfl

/-- Identity isomorphism. -/
@[refl]
def refl (X : C) : X ≅ X where
  hom := 𝟙 X
  inv := 𝟙 X

@[simp, grind =]
theorem refl_hom (X : C) : (Iso.refl X).hom = 𝟙 X := rfl
@[simp, grind =]
theorem refl_inv (X : C) : (Iso.refl X).inv = 𝟙 X := rfl

instance : Inhabited (X ≅ X) := ⟨Iso.refl X⟩

/-- Composition of two isomorphisms -/
def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where
  hom := α.hom ≫ β.hom
  inv := β.inv ≫ α.inv

/-- Notation for composition of isomorphisms. -/
infixr:80 " ≪≫ " => Iso.trans

@[grind =] theorem trans_hom (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).hom = α.hom ≫ β.hom := rfl
@[grind =] theorem trans_inv (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).inv = β.inv ≫ α.inv := rfl

instance instTransIso : Trans (α := C) (· ≅ ·) (· ≅ ·) (· ≅ ·) where
  trans := trans

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
  protected left_inv : LeftInverse invFun toFun := by grind
  protected right_inv : RightInverse invFun toFun := by grind

@[inherit_doc]
infixl:25 " ≃ " => Equiv

attribute [local grind] Function.LeftInverse Function.RightInverse in
/-- The bijection `(Z ⟶ X) ≃ (Z ⟶ Y)` induced by `α : X ≅ Y`. -/
def homToEquiv (α : X ≅ Y) {Z : C} : (Z ⟶ X) ≃ (Z ⟶ Y) where
  toFun f := f ≫ α.hom
  invFun g := g ≫ α.inv

end Iso

/-- `IsIso` typeclass expressing that a morphism is invertible. -/
class IsIso (f : X ⟶ Y) : Prop where
  /-- The existence of an inverse morphism. -/
  out : ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

/-- The inverse of a morphism `f` when we have `[IsIso f]`.
-/
noncomputable def inv (f : X ⟶ Y) [I : IsIso f] : Y ⟶ X :=
  Classical.choose I.1

namespace IsIso

@[simp, grind =]
theorem hom_inv_id (f : X ⟶ Y) [I : IsIso f] : f ≫ inv f = 𝟙 X :=
  (Classical.choose_spec I.1).left

@[simp, grind =]
theorem inv_hom_id (f : X ⟶ Y) [I : IsIso f] : inv f ≫ f = 𝟙 Y :=
  (Classical.choose_spec I.1).right

end IsIso

theorem Iso.isIso_hom (e : X ≅ Y) : IsIso e.hom :=
  ⟨e.inv, by simp, by simp⟩

theorem Iso.isIso_inv (e : X ≅ Y) : IsIso e.inv :=
  ⟨e.hom, by simp, by simp⟩

attribute [instance] Iso.isIso_hom Iso.isIso_inv

open IsIso

/-- Reinterpret a morphism `f` with an `IsIso f` instance as an `Iso`. -/
noncomputable def asIso (f : X ⟶ Y) [IsIso f] : X ≅ Y :=
  ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

@[simp, grind =]
theorem asIso_hom (f : X ⟶ Y) {_ : IsIso f} : (asIso f).hom = f :=
  rfl

@[simp, grind =]
theorem asIso_inv (f : X ⟶ Y) {_ : IsIso f} : (asIso f).inv = inv f :=
  rfl

namespace IsIso

@[grind ←=]
theorem inv_eq_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    inv f = g := by
  have := congrArg (inv f ≫ ·) hom_inv_id
  grind

theorem inv_eq_of_inv_hom_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (inv_hom_id : g ≫ f = 𝟙 Y) :
    inv f = g := by
  have := congrArg (· ≫ inv f) inv_hom_id
  grind

theorem eq_inv_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    g = inv f :=
  (inv_eq_of_hom_inv_id hom_inv_id).symm

theorem eq_inv_of_inv_hom_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (inv_hom_id : g ≫ f = 𝟙 Y) :
    g = inv f :=
  (inv_eq_of_inv_hom_id inv_hom_id).symm

instance inv_isIso {f : X ⟶ Y} [IsIso f] : IsIso (inv f) :=
  { out := ⟨f, by simp, by simp⟩ }

end IsIso

namespace Iso

variable (e : X ≅ Y)

@[grind =]
theorem map_hom_inv_id (F : C ⥤ D) :
    F.map e.hom ≫ F.map e.inv = 𝟙 _ := by grind

@[grind =]
theorem map_inv_hom_id (F : C ⥤ D) :
    F.map e.inv ≫ F.map e.hom = 𝟙 _ := by grind

end Iso

namespace Functor

variable {D : Type u₂}
variable [Category.{v₂} D]

/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
def mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  hom := F.map i.hom
  inv := F.map i.inv

@[simp, grind =]
theorem mapIso_hom (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : (F.mapIso i).hom = F.map i.hom := rfl
@[simp, grind =]
theorem mapIso_inv (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : (F.mapIso i).inv = F.map i.inv := rfl

@[simp]
theorem mapIso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.mapIso i.symm = (F.mapIso i).symm :=
  rfl

@[simp]
theorem mapIso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
    F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j := by
  ext; apply Functor.map_comp

@[simp]
theorem mapIso_refl (F : C ⥤ D) (X : C) : F.mapIso (Iso.refl X) = Iso.refl (F.obj X) :=
  Iso.ext <| F.map_id X

instance map_isIso (F : C ⥤ D) (f : X ⟶ Y) [IsIso f] : IsIso (F.map f) :=
  (F.mapIso (asIso f)).isIso_hom

@[simp]
theorem map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map (inv f) = inv (F.map f) := by
  apply eq_inv_of_hom_inv_id
  simp [← F.map_comp]

theorem map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) := by simp

theorem map_inv_hom (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    F.map (inv f) ≫ F.map f = 𝟙 (F.obj Y) := by simp

end Functor

end Mathlib.CategoryTheory.Iso

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

theorem naturality_app {F G : Functor C (Functor D E)} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
    (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z := by
  grind -- this is done manually in Mathlib!
  -- rw [← comp_app]
  -- rw [T.naturality f]
  -- rw [comp_app]

@[simp]
theorem vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.vcomp α β = α ≫ β := rfl

theorem vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X := rfl

theorem congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by grind

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
  grind

theorem naturality_app_app {F G : C ⥤ D ⥤ E ⥤ E'}
    (α : F ⟶ G) {X₁ Y₁ : C} (f : X₁ ⟶ Y₁) (X₂ : D) (X₃ : E) :
    ((F.map f).app X₂).app X₃ ≫ ((α.app Y₁).app X₂).app X₃ =
      ((α.app X₁).app X₂).app X₃ ≫ ((G.map f).app X₂).app X₃ := by
  grind

end NatTrans

namespace Functor

/-- Flip the arguments of a bifunctor. See also `Currying.lean`. -/
protected def flip (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E where
  obj k :=
    { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }

@[simp] theorem flip_obj_obj (F : C ⥤ D ⥤ E) (k : D) : (F.flip.obj k).obj = fun j => (F.obj j).obj k := rfl
@[simp] theorem flip_obj_map (F : C ⥤ D ⥤ E) (k : D) {X Y : C}(f : X ⟶ Y) : (F.flip.obj k).map f = (F.map f).app k := rfl
@[simp] theorem flip_map_app (F : C ⥤ D ⥤ E) {X Y : D} (f : X ⟶ Y) (k : C) : (F.flip.map f).app k = (F.obj k).map f := rfl

attribute [grind =] flip_obj_obj flip_obj_map flip_map_app

end Functor

variable (C D E) in
/-- The functor `(C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E` which flips the variables. -/
def flipFunctor : (C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E where
  obj F := F.flip
  map {F₁ F₂} φ := { app := fun Y => { app := fun X => (φ.app X).app Y } }

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

section Mathlib.CategoryTheory.NatIso


open NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

namespace Iso

/-- The application of a natural isomorphism to an object. We put this definition in a different
namespace, so that we can use `α.app` -/
def app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    F.obj X ≅ G.obj X where
  hom := α.hom.app X
  inv := α.inv.app X
  hom_inv_id := by rw [← comp_app, Iso.hom_inv_id]; rfl
  inv_hom_id := by rw [← comp_app, Iso.inv_hom_id]; rfl

@[simp, grind =] theorem app_hom {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).hom = α.hom.app X := rfl
@[simp, grind =] theorem app_inv {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).inv = α.inv.app X := rfl

@[simp, grind =]
theorem hom_inv_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    α.hom.app X ≫ α.inv.app X = 𝟙 (F.obj X) :=
  congrFun (congrArg NatTrans.app α.hom_inv_id) X

@[simp, grind =]
theorem inv_hom_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    α.inv.app X ≫ α.hom.app X = 𝟙 (G.obj X) :=
  congrFun (congrArg NatTrans.app α.inv_hom_id) X

@[simp]
theorem hom_inv_id_app_app {F G : C ⥤ D ⥤ E} (e : F ≅ G) (X₁ : C) (X₂ : D) :
    (e.hom.app X₁).app X₂ ≫ (e.inv.app X₁).app X₂ = 𝟙 _ := by
  rw [← NatTrans.comp_app, Iso.hom_inv_id_app, NatTrans.id_app]

@[simp]
theorem inv_hom_id_app_app {F G : C ⥤ D ⥤ E} (e : F ≅ G) (X₁ : C) (X₂ : D) :
    (e.inv.app X₁).app X₂ ≫ (e.hom.app X₁).app X₂ = 𝟙 _ := by
  rw [← NatTrans.comp_app, Iso.inv_hom_id_app, NatTrans.id_app]

@[simp]
theorem hom_inv_id_app_app_app {F G : C ⥤ D ⥤ E ⥤ E'} (e : F ≅ G)
    (X₁ : C) (X₂ : D) (X₃ : E) :
    ((e.hom.app X₁).app X₂).app X₃ ≫ ((e.inv.app X₁).app X₂).app X₃ = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, Iso.hom_inv_id_app,
    NatTrans.id_app, NatTrans.id_app]

@[simp]
theorem inv_hom_id_app_app_app {F G : C ⥤ D ⥤ E ⥤ E'} (e : F ≅ G)
    (X₁ : C) (X₂ : D) (X₃ : E) :
    ((e.inv.app X₁).app X₂).app X₃ ≫ ((e.hom.app X₁).app X₂).app X₃ = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, Iso.inv_hom_id_app,
    NatTrans.id_app, NatTrans.id_app]

end Iso

namespace NatIso

open CategoryTheory.Category CategoryTheory.Functor

@[simp]
theorem trans_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) :
    (α ≪≫ β).app X = α.app X ≪≫ β.app X :=
  rfl

variable {F G : C ⥤ D}

instance hom_app_isIso (α : F ≅ G) (X : C) : IsIso (α.hom.app X) :=
  ⟨⟨α.inv.app X, ⟨by grind, by grind⟩⟩⟩

instance inv_app_isIso (α : F ≅ G) (X : C) : IsIso (α.inv.app X) :=
  ⟨⟨α.hom.app X, ⟨by grind, by grind⟩⟩⟩

section

variable (α : F ≅ G)

@[simp]
theorem inv_inv_app {F G : C ⥤ D} (e : F ≅ G) (X : C) : inv (e.inv.app X) = e.hom.app X := by
  grind

end

variable {X Y : C}

theorem naturality_1 (α : F ≅ G) (f : X ⟶ Y) : α.inv.app X ≫ F.map f ≫ α.hom.app Y = G.map f := by
  grind

theorem naturality_2 (α : F ≅ G) (f : X ⟶ Y) : α.hom.app X ≫ G.map f ≫ α.inv.app Y = F.map f := by
  grind

theorem naturality_1' (α : F ⟶ G) (f : X ⟶ Y) {_ : IsIso (α.app X)} :
    inv (α.app X) ≫ F.map f ≫ α.app Y = G.map f := by grind

@[simp]
theorem naturality_2' (α : F ⟶ G) (f : X ⟶ Y) {_ : IsIso (α.app Y)} :
    α.app X ≫ G.map f ≫ inv (α.app Y) = F.map f := by
  grind

/-- The components of a natural isomorphism are isomorphisms.
-/
instance isIso_app_of_isIso (α : F ⟶ G) [IsIso α] (X) : IsIso (α.app X) :=
  ⟨⟨(inv α).app X, ⟨by grind, by grind⟩⟩⟩

@[simp]
theorem isIso_inv_app (α : F ⟶ G) {_ : IsIso α} (X) : (inv α).app X = inv (α.app X) := by
  grind

@[simp]
theorem inv_map_inv_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
    inv ((F.map e.inv).app Z) = (F.map e.hom).app Z := by
  grind

/-- Construct a natural isomorphism between functors by giving object level isomorphisms,
and checking naturality only in the forward direction.
-/
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by grind) :
    F ≅ G where
  hom := { app := fun X => (app X).hom }
  inv :=
    { app := fun X => (app X).inv,
      naturality := fun X Y f => by
        have h := congrArg (fun f => (app X).inv ≫ f ≫ (app Y).inv) (naturality f).symm
        grind }
  hom_inv_id := by
    grind
  inv_hom_id := by
    grind

@[simp, grind =]
theorem ofComponents_hom_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X : C) :
    (ofComponents app naturality).hom.app X = (app X).hom := rfl
@[simp, grind =]
theorem ofComponents_inv_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X : C) :
    (ofComponents app naturality).inv.app X = (app X).inv := rfl

theorem ofComponents_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X : C) :
    (ofComponents app naturality).app X = app X := by
  grind

@[simp]
theorem ofComponents.app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
    (ofComponents app naturality).app X = app X := by grind

-- Making this an instance would cause a typeclass inference loop with `isIso_app_of_isIso`.
/-- A natural transformation is an isomorphism if all its components are isomorphisms.
-/
theorem isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  (ofComponents (fun X => asIso (α.app X)) (by simp)).isIso_hom

/-- Horizontal composition of natural isomorphisms. -/
def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I := by
  refine ⟨α.hom ◫ β.hom, α.inv ◫ β.inv, ?_, ?_⟩
  · ext
    rw [← NatTrans.exchange]
    simp
  · ext
    rw [← NatTrans.exchange]
    simp

@[simp]
theorem hcomp_hom {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) :
    (hcomp α β).hom = α.hom ◫ β.hom := rfl
@[simp]
theorem hcomp_inv {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) :
    (hcomp α β).inv = α.inv ◫ β.inv := rfl

theorem isIso_map_iff {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y) :
    IsIso (F₁.map f) ↔ IsIso (F₂.map f) := by
  revert F₁ F₂
  suffices ∀ {F₁ F₂ : C ⥤ D} (_ : F₁ ≅ F₂) (_ : IsIso (F₁.map f)), IsIso (F₂.map f) by
    exact fun F₁ F₂ e => ⟨this e, this e.symm⟩
  intro F₁ F₂ e hf
  refine IsIso.mk ⟨e.inv.app Y ≫ inv (F₁.map f) ≫ e.hom.app X, ?_, ?_⟩
  · grind (ematch := 6)
  · grind (ematch := 7)

end NatIso

theorem NatTrans.isIso_iff_isIso_app {F G : C ⥤ D} (τ : F ⟶ G) :
    IsIso τ ↔ ∀ X, IsIso (τ.app X) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ NatIso.isIso_of_isIso_app _⟩

end Mathlib.CategoryTheory.NatIso

end CategoryTheory
