namespace MWE
opaque P : {n : Nat} → Fin (n+1) → Prop
axiom Pax : @P n 0
example (a : Fin 3) : a = 0 → P a := by
  grind [Pax]
end MWE

-- Inline Opposite from Mathlib.Data.Opposite
structure Opposite (α : Sort _) where
  op ::
  unop : α

notation:max α "ᵒᵖ" => Opposite α

-- Inline Quiver from Mathlib.Combinatorics.Quiver.Basic
class Quiver.{u,v} (V : Type u) where
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

namespace Quiver
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (b.unop ⟶ a.unop)ᵒᵖ⟩

def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : Opposite.op Y ⟶ Opposite.op X := Opposite.op f
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : Y.unop ⟶ X.unop := Opposite.unop f
end Quiver

-- Inline CategoryTheory from Mathlib.CategoryTheory.Category.Basic
namespace CategoryTheory
open Quiver

class CategoryStruct (obj : Type _) extends Quiver obj where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

scoped notation "𝟙" => CategoryStruct.id
scoped infixr:80 " ≫ " => CategoryStruct.comp

class Category (obj : Type _) extends CategoryStruct obj where

abbrev LargeCategory (C : Type _) := Category C
abbrev SmallCategory (C : Type _) := Category C

-- Inline Functor from Mathlib.CategoryTheory.Functor.Basic
structure Functor (C D : Type _) [Category C] [Category D] where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y))

scoped infixr:26 " ⥤ " => Functor
end CategoryTheory

-- Inline Preorder from Mathlib.Order.Defs.PartialOrder
class Preorder (α : Type _) extends LE α, LT α where

open Opposite CategoryTheory

-- Inline from Mathlib.CategoryTheory.InducedCategory
section InducedCategory
variable {C : Type _} (D : Type _) [Category D] (F : C → D)

def InducedCategory (_F : C → D) : Type _ := C

instance InducedCategory.category : Category (InducedCategory D F) where
  Hom X Y := F X ⟶ F Y
  id X := 𝟙 (F X)
  comp f g := f ≫ g

end InducedCategory

-- Inline from Mathlib.CategoryTheory.ObjectProperty.Basic
abbrev ObjectProperty (C : Type _) [CategoryStruct C] : Type _ := C → Prop

-- Inline from Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
namespace ObjectProperty
variable {C : Type _} [Category C]

structure FullSubcategory (P : ObjectProperty C) where
  obj : C
  property : P obj

instance FullSubcategory.category (P : ObjectProperty C) : Category (FullSubcategory P) :=
  InducedCategory.category C FullSubcategory.obj

end ObjectProperty

-- Inline from Mathlib.CategoryTheory.Opposites
section Opposites
variable {C : Type _} [CategoryStruct.{0} C]

instance CategoryStruct.opposite : CategoryStruct Cᵒᵖ where
  comp f g := (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op

variable [Category C]

instance Category.opposite : Category Cᵒᵖ where

@[grind? _=_]
theorem op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).op = g.op ≫ f.op := rfl

end Opposites

-- Inline OrderHom minimally
structure OrderHom (α β : Type _) [Preorder α] [Preorder β] where
  toFun : α → β
  monotone' : ∀ ⦃a b⦄, a ≤ b → toFun a ≤ toFun b

infixr:25 " →o " => OrderHom

namespace OrderHom
variable {α β γ : Type _} [Preorder α] [Preorder β] [Preorder γ]

instance : CoeFun (α →o β) fun _ => α → β := ⟨OrderHom.toFun⟩

def id : α →o α := ⟨_root_.id, fun _ _ h => h⟩

def comp (g : β →o γ) (f : α →o β) : α →o γ :=
  ⟨g ∘ f, fun _ _ h => g.monotone' (f.monotone' h)⟩

end OrderHom

structure OrderEmbedding (α β : Type _) [LE α] [LE β] where
  toFun : α → β
  inj' : Function.Injective toFun

infixl:25 " ↪o " => OrderEmbedding

namespace OrderEmbedding
variable {α β : Type _} [Preorder α] [Preorder β]

def toOrderHom (f : α ↪o β) : α →o β :=
  ⟨f.toFun, sorry⟩

end OrderEmbedding

-- Inline Fin Preorder instance
instance : Preorder (Fin n) where
  le := (· ≤ ·)
  lt := (· < ·)

-- Inline Fin functions
namespace Fin

def succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if castSucc i < p then i.castSucc else i.succ

def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if castSucc p < i then i.pred sorry else i.cast sorry

def predAboveOrderHom (p : Fin n) : Fin (n + 1) →o Fin n :=
  ⟨p.predAbove, sorry⟩

def succAboveOrderEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  ⟨p.succAbove, sorry⟩

end Fin

open CategoryTheory

-- Inline from Mathlib.CategoryTheory.Types.Basic
instance types : LargeCategory (Type _) where
  Hom a b := a → b
  id _ := id
  comp f g := g ∘ f
namespace FunctorToTypes

variable {C : Type _} [Category C] (F : C ⥤ Type) {X Y Z : C}

theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) :
    (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) := sorry

end FunctorToTypes
section Mathlib.AlgebraicTopology.SimplexCategory.Defs

def SimplexCategory := Nat
namespace SimplexCategory

def mk (n : Nat) : SimplexCategory := n
notation "⦋" n "⦌" => SimplexCategory.mk n
def len (n : SimplexCategory) : Nat := n

protected def Hom (a b : SimplexCategory) := Fin (a.len + 1) →o Fin (b.len + 1)
namespace Hom

def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) : SimplexCategory.Hom a b := f
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : Fin (a.len + 1) →o Fin (b.len + 1) := f

def id (a : SimplexCategory) : SimplexCategory.Hom a a := mk OrderHom.id
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c := mk <| f.toOrderHom.comp g.toOrderHom

end Hom

instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id _ := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

end SimplexCategory

end Mathlib.AlgebraicTopology.SimplexCategory.Defs
section Mathlib.AlgebraicTopology.SimplexCategory.Basic
namespace SimplexCategory

def δ {n} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.Hom.mk (Fin.succAboveOrderEmb i).toOrderHom

def σ {n} (i : Fin (n + 1)) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk i.predAboveOrderHom

end SimplexCategory

end Mathlib.AlgebraicTopology.SimplexCategory.Basic

abbrev SimplexCategory.Truncated' (n : Nat) := ObjectProperty.FullSubcategory fun a : SimplexCategory => a.len ≤ n
abbrev δ' (m : Nat) {n} (i : Fin (n + 2)) (hn) (hn') :
  (⟨⦋n⦌, hn⟩ : SimplexCategory.Truncated' m) ⟶ ⟨⦋n + 1⦌, hn'⟩ := SimplexCategory.δ i
abbrev σ' (m : Nat) {n} (i : Fin (n + 1)) (hn) (hn') :
    (⟨⦋n + 1⦌, hn⟩ : SimplexCategory.Truncated' m) ⟶ ⟨⦋n⦌, hn'⟩ := SimplexCategory.σ i
abbrev δ₂' {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) := δ' 2 i hn hn'
abbrev σ₂' {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) := σ' 2 i hn hn'
theorem δ₂_zero_comp_σ₂_zero' {n} (hn) (hn') :
    δ₂' (n := n) 0 hn hn' ≫ σ₂' 0 hn' hn = 𝟙 _ := sorry

def SSet.Truncated' (n : Nat) := (SimplexCategory.Truncated' n)ᵒᵖ ⥤ Type

/--
error: `grind` failed
case grind
X : SSet.Truncated' 2
Δ : X.obj { unop := { obj := ⦋1⦌, property := ⋯ } }
h : ¬X.map (SimplexCategory.δ 0).op (X.map (SimplexCategory.σ 0).op Δ) = Δ
⊢ False
use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (X : SSet.Truncated' 2) (Δ : X.obj (Opposite.op ⟨⦋1⦌, by decide⟩)) :
    X.map (δ₂' 0).op (X.map (σ₂' 0).op Δ) = Δ := by
  grind -verbose [_=_ FunctorToTypes.map_comp_apply, δ₂_zero_comp_σ₂_zero']
