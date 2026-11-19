module

set_option warn.classDefReducibility false
@[expose] public section
-- import Lean.Meta.Tactic.Grind
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

infixr:26 " ⥤ " => Functor

attribute [simp] Functor.map_id Functor.map_comp

attribute [grind =] Functor.map_id
attribute [grind _=_] Functor.map_comp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable {F G H : Functor C D}

namespace Functor

def comp (F : Functor C D) (G : Functor D E) : Functor C E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  -- Note `map_id` and `map_comp` are handled by `cat_tac`.

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

attribute [grind ext] NatTrans.ext

attribute [simp, grind =] NatTrans.naturality

namespace NatTrans

variable {X : C}

protected def id (F : Functor C D) : NatTrans F F where app X := 𝟙 (F.obj X)

@[simp, grind =] theorem id_app : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

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
  -- Here we're okay: all the proofs are handled by `cat_tac`.

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
    α.inv = α.inv ≫ β.hom ≫ β.inv   := by grind
    _     = β.inv                    := by grind


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


variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- Perhaps in the future we could redefine `Functor` in terms of this, but that isn't the
-- immediate plan.
/-- An unbundled functor. -/
class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  /-- A functorial map extends to an action on morphisms. -/
  map' : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  /-- A functorial map preserves identities. -/
  map_id' : ∀ X : C, map' (𝟙 X) = 𝟙 (F X) := by grind
  /-- A functorial map preserves composition of morphisms. -/
  map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map' (f ≫ g) = map' f ≫ map' g := by
    grind

def map (F : C → D) [Functorial.{v₁, v₂} F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
  Functorial.map'.{v₁, v₂} f

@[simp, grind =]
theorem map'_as_map {F : C → D} [Functorial.{v₁, v₂} F] {X Y : C} {f : X ⟶ Y} :
    Functorial.map'.{v₁, v₂} f = map F f :=
  rfl

@[simp, grind =]
theorem Functorial.map_id {F : C → D} [Functorial.{v₁, v₂} F] {X : C} : map F (𝟙 X) = 𝟙 (F X) :=
  Functorial.map_id' X

@[simp, grind =]
theorem Functorial.map_comp {F : C → D} [Functorial.{v₁, v₂} F] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} : map F (f ≫ g) = map F f ≫ map F g :=
  Functorial.map_comp' f g

namespace Functor

/-- Bundle a functorial function as a functor.
-/
def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with
    obj := F
    map := CategoryTheory.map F }

end Functor

instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with map' := F.map }

@[simp, grind =]
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl

attribute [grind] _root_.id

instance functorial_id : Functorial.{v₁, v₁} (id : C → C) where map' f := f

namespace Ex1
variable {E : Type u₃} [Category.{v₃} E]

def functorial_comp (F : C → D) [Functorial.{v₁, v₂} F] (G : D → E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with
    map' := fun f => map G (map F f)
    map_id' := sorry
    map_comp' := by grind
  }
end Ex1

end CategoryTheory
