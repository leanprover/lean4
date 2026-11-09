
namespace Test

class CategoryStruct (obj : Type) where
  Hom : obj → obj → Type
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (Hom X Y) → (Hom Y Z) → (Hom X Z)

variable (ι : Type) (V : Type) [CategoryStruct V]

notation (priority := high) "𝟙" => CategoryStruct.id
infixr:10 (priority := high) " ⟶ " => CategoryStruct.Hom

structure Functor (C : Type) [CategoryStruct C] (D : Type) [CategoryStruct D] where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)


structure HomologicalComplex where
  X : ι → V

@[ext]
structure Hom (A B : HomologicalComplex ι V) where
  f : ∀ i, A.X i ⟶ B.X i

def id (A : HomologicalComplex ι V) : Hom ι V A A where f _ := 𝟙 _


instance : CategoryStruct (HomologicalComplex ι V) where
  Hom A B := Test.Hom ι V A B
  id _ := { f := fun _ => 𝟙 _ }
  comp f g := { f := fun i => CategoryStruct.comp (f.f i) (g.f i) }

@[simp] theorem ha {A : HomologicalComplex ι V} {i} : Test.Hom.f (𝟙 A) i = 𝟙 _ := rfl

@[ext]
theorem hom_ext {C D : HomologicalComplex ι V} (f g : C ⟶ D)
    (h : ∀ i, f.f i = g.f i) : f = g := by
  apply Hom.ext
  funext
  apply h

variable [OfNat V 0] [DecidableEq ι] [∀ a b : V, Zero (a ⟶ b)]

/--
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
noncomputable def single'' (j : ι) : Functor V (HomologicalComplex ι V) where
  obj A :=
    { X := fun i => if i = j then A else 0  }
  map f :=  { f := fun i => if h : i = j then sorry else 0 }
  map_id A := by
    ext i
    dsimp [Functor.map_id]
    by_cases h : ¬i = j
    · rw [if_neg h]
      sorry
    · sorry
