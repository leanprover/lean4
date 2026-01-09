/-!
This is a failure of automation in `Mathlib.Algebra.Category.GroupCat.Adjunctions`.

Here `dsimp at *` is not successfully reducing a projection of a constructor,
while `dsimp at x` succeeds.

In this particular example it doesn't really matter,
but in more complicated examples this then prevents later simp lemmas firing,
and requires manual work.
-/

section Mathlib.Data.FunLike.Basic

class DFunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  coe : F → ∀ a : α, β a

abbrev FunLike F α β := DFunLike F α fun _ => β

variable (F α : Sort _) (β : α → Sort _)

namespace DFunLike

variable {F α β} [i : DFunLike F α β]

instance hasCoeToFun : CoeFun F (fun _ ↦ ∀ a : α, β a) where
  coe := @DFunLike.coe _ _ β _

end DFunLike

end Mathlib.Data.FunLike.Basic

section Mathlib.Algebra.Group.Defs

universe u

class Monoid (M : Type u) where
  one : M

class Group (G : Type u) extends Monoid G where

class CommGroup (G : Type u) extends Group G

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.Group.Hom.Defs

variable {M N P : Type _}

section mul_one

variable [Monoid M] [Monoid N]

structure MonoidHom (M : Type _) (N : Type _) [Monoid M] [Monoid N] where
  protected toFun : M → N

infixr:25 " →* " => MonoidHom

instance MonoidHom.instFunLike : FunLike (M →* N) M N where
  coe f := f.toFun

end mul_one

theorem MonoidHom.ext [Monoid M] [Monoid N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
  sorry

def MonoidHom.id (M : Type _) [Monoid M] : M →* M where
  toFun x := x

def MonoidHom.comp [Monoid M] [Monoid N] [Monoid P] (hnp : N →* P) (hmn : M →* N) :
    M →* P where
  toFun := hnp ∘ hmn

end Mathlib.Algebra.Group.Hom.Defs

section Mathlib.Data.FunLike.Equiv

class EquivLike (E : Sort _) (α β : outParam (Sort _)) where
  coe : E → α → β

namespace EquivLike

variable {E F α β γ : Sort _} [iE : EquivLike E α β] [iF : EquivLike F β γ]

instance (priority := 100) toFunLike : FunLike E α β where
  coe := (coe : E → α → β)

end EquivLike

end Mathlib.Data.FunLike.Equiv

section Mathlib.Logic.Equiv.Defs

universe u v

variable {α : Sort u} {β : Sort v}

structure Equiv (α : Sort _) (β : Sort _) where
  protected toFun : α → β
  protected invFun : β → α

infixl:25 " ≃ " => Equiv

namespace Equiv

instance : EquivLike (α ≃ β) α β where
  coe := Equiv.toFun

end Equiv

end Mathlib.Logic.Equiv.Defs

section Mathlib.GroupTheory.Abelianization

universe u

def Abelianization (G : Type u) [Group G] : Type u := sorry

variable (G : Type u) [Group G]

namespace Abelianization

instance commGroup : CommGroup (Abelianization G) := sorry

variable {G}

def of : G →* Abelianization G := sorry

variable {A : Type u} [CommGroup A] (f : G →* A)

def lift : (G →* A) ≃ (Abelianization G →* A) := sorry

end Abelianization

end Mathlib.GroupTheory.Abelianization

section Mathlib.CategoryTheory.ConcreteCategory.Bundled

universe u v

namespace CategoryTheory

variable {c : Type u → Type v} {α : Type u}

structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
  α : Type u
  str : c α

namespace Bundled

set_option checkBinderAnnotations false in
def of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩

instance coeSort : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩

end Bundled

end CategoryTheory

end Mathlib.CategoryTheory.ConcreteCategory.Bundled

section Mathlib.Combinatorics.Quiver.Basic

universe v v₁ v₂ u u₁ u₂

class Quiver (V : Type u) where
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

infixl:50 " ⥤q " => Prefunctor

end Mathlib.Combinatorics.Quiver.Basic

section Mathlib.CategoryTheory.Category.Basic

universe v u

namespace CategoryTheory

class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  id : ∀ X : obj, Hom X X

scoped notation "𝟙" => CategoryStruct.id

class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where

abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) := Category.{u} C

end CategoryTheory

end Mathlib.CategoryTheory.Category.Basic

section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)

infixr:26 " ⥤ " => Functor

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory


section Mathlib.CategoryTheory.ConcreteCategory.BundledHom

universe u

namespace CategoryTheory

variable {c : Type u → Type u} (hom : ∀ ⦃α β : Type u⦄ (_ : c α) (_ : c β), Type u)

structure BundledHom where
  toFun : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β
  id : ∀ {α : Type u} (I : c α), hom I I

attribute [class] BundledHom

namespace BundledHom

variable [𝒞 : BundledHom hom]

set_option synthInstance.checkSynthOrder false in
instance category : Category (Bundled c) where
  Hom := fun X Y => hom X.str Y.str
  id := fun X => BundledHom.id 𝒞 (α := X) X.str

variable {d : Type u → Type u}

abbrev MapHom (F : ∀ {α}, d α → c α) : ∀ ⦃α β : Type u⦄ (_ : d α) (_ : d β), Type u :=
  fun _ _ iα iβ => hom (F iα) (F iβ)

def map (F : ∀ {α}, d α → c α) : BundledHom (MapHom hom @F)
    where
  toFun α β {iα} {iβ} f := 𝒞.toFun (F iα) (F iβ) f
  id α {iα} := sorry

class ParentProjection (F : ∀ {α}, d α → c α) : Prop

instance bundledHomOfParentProjection (F : ∀ {α}, d α → c α) [ParentProjection @F] :
    BundledHom (MapHom hom @F) :=
  map hom @F

end BundledHom

end CategoryTheory

end Mathlib.CategoryTheory.ConcreteCategory.BundledHom

section Mathlib.Algebra.Category.MonCat.Basic

namespace MonCat

abbrev AssocMonoidHom (M N : Type _) [Monoid M] [Monoid N] :=
  MonoidHom M N

instance bundledHom : BundledHom AssocMonoidHom where
  toFun _ _ f := ⇑f
  id _ := MonoidHom.id _

end MonCat

end Mathlib.Algebra.Category.MonCat.Basic

section Mathlib.Algebra.Category.GroupCat.Basic

universe u

def GroupCat : Type (u + 1) := Bundled Group

namespace GroupCat

instance : BundledHom.ParentProjection
  (fun {α : Type _} (h : Group α) => h.toMonoid) := ⟨⟩

deriving instance LargeCategory for GroupCat

instance : CoeSort GroupCat (Type _) where
  coe X := X.α

instance (X : GroupCat) : Group X := X.str

instance {X Y : GroupCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

end GroupCat

def CommGroupCat : Type (u + 1) :=
  Bundled CommGroup

namespace CommGroupCat

instance : BundledHom.ParentProjection @CommGroup.toGroup := ⟨⟩

deriving instance LargeCategory for CommGroupCat

instance : CoeSort CommGroupCat (Type _) where
  coe X := X.α

instance commGroupInstance (X : CommGroupCat) : CommGroup X := X.str

instance {X Y : CommGroupCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[ext]
theorem ext {X Y : CommGroupCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

def of (G : Type u) [CommGroup G] : CommGroupCat :=
  Bundled.of G

end CommGroupCat

end Mathlib.Algebra.Category.GroupCat.Basic

section Mathlib.Algebra.Category.GroupCat.Adjunctions

universe u

def abelianize : GroupCat.{u} ⥤ CommGroupCat.{u} where
  obj G := CommGroupCat.of (Abelianization G)
  map f := Abelianization.lift (Abelianization.of.comp f)
  map_id := by
    intros G
    ext x
    guard_hyp x :ₛ
      ↑({ obj := fun G ↦ CommGroupCat.of (Abelianization ↑G),
          map := fun {X Y} f ↦ Abelianization.lift (Abelianization.of.comp f) : GroupCat ⥤q CommGroupCat}.obj G : Type u)
    dsimp at * -- `dsimp at *` does less than `dsimp at x ⊢` :-(
    guard_hyp x :ₛ (CommGroupCat.of (Abelianization G) : Type u)
    dsimp at x ⊢
    guard_hyp x :ₛ (CommGroupCat.of (Abelianization G) : Type u)
    sorry

end Mathlib.Algebra.Category.GroupCat.Adjunctions
