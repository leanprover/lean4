/-!
# Motivating example for the `[implicit_reducible]` / `[instance_reducible]` split

A cut-down model of Mathlib's category theory library. Composition of functors `F ⋙ G`
is defined by `Functor.comp`, and we want `Functor.comp` to unfold during implicit-argument
definitional equality (so that `rw` lemmas about `⋙` apply) *without* unfolding during type
class synthesis (so that data-carrying instances on `(F ⋙ G) ⋙ H` and `F ⋙ (G ⋙ H)` stay
distinct).

The `[implicit_reducible]` reducibility level delivers exactly this: marking `Functor.comp` with
`@[implicit_reducible]` makes `whiskerLeft''` elaborate, while a `Foo` instance on one
association is *not* found for the other.
-/

section Mathlib.Combinatorics.Quiver.Basic

class Quiver (V : Type) where
  Hom : V → V → Type

infixr:10 " ⟶ " => Quiver.Hom

end Mathlib.Combinatorics.Quiver.Basic

section Mathlib.CategoryTheory.Category.Basic

namespace CategoryTheory

class Category (obj : Type) extends Quiver obj where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

notation "𝟙" => Category.id

infixr:80 " ≫ " => Category.comp

end CategoryTheory

end Mathlib.CategoryTheory.Category.Basic

section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

structure Functor (C : Type) [Category C] (D : Type) [Category D] where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y))

infixr:26 " ⥤ " => Functor

namespace Functor

variable {C : Type} [Category C] {D : Type} [Category D] {E : Type} [Category E]

def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := sorry

infixr:80 " ⋙ " => Functor.comp

theorem comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := sorry

end Functor

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Basic

section Mathlib.CategoryTheory.NatTrans

namespace CategoryTheory

variable {C : Type} [Category C] {D : Type} [Category D]

structure NatTrans (F G : C ⥤ D) where
  app (X : C) : F.obj X ⟶ G.obj X
  naturality ⦃X Y : C⦄ (f : X ⟶ Y) : F.map f ≫ app Y = app X ≫ G.map f := by sorry

namespace NatTrans

def id (F : C ⥤ D) : NatTrans F F where
  app X := sorry
  naturality := sorry

theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := sorry

section

variable {F G H : C ⥤ D}

def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := sorry

end

end NatTrans

end CategoryTheory

end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory

open NatTrans

variable {C : Type} [Category C] {D : Type} [Category D]

instance Functor.category : Category (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Category

open CategoryTheory

variable {C : Type} [Category C] {D : Type} [Category D] {E : Type} [Category E]

/-! We would like this to work without `backward.isDefEq.respectTransparency`: -/
/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  G.map ?f ≫ α.app ?Y
in the target expression
  G.map (F.map f) ≫ α.app (F.obj Y) = α.app (F.obj X) ≫ H.map (F.map f)

C : Type
inst✝² : Category C
D : Type
inst✝¹ : Category D
E : Type
inst✝ : Category E
F : C ⥤ D
G H : D ⥤ E
α : G ⟶ H
X Y : C
f : X ⟶ Y
⊢ G.map (F.map f) ≫ α.app (F.obj Y) = α.app (F.obj X) ≫ H.map (F.map f)

Note: The target expression is not type-correct under the `instances` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    G.map (F.map f)
  has type
    @Quiver.Hom E inst✝.toQuiver (G.obj (F.obj X)) (G.obj (F.obj Y))
  but is expected to have type
    @Quiver.Hom E inst✝.toQuiver ((F ⋙ G).obj X) ((F ⋙ G).obj Y)
  in the application
    Category.comp (G.map (F.map f))
-/
#guard_msgs in
def whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

#guard_msgs in
set_option backward.isDefEq.respectTransparency false in
def whiskerLeft' (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

/-! We can achieve this by marking `Functor.comp` with `implicit_reducible`: -/
attribute [local implicit_reducible] Functor.comp in
def whiskerLeft'' (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

/-!
However in the category theory library we need to be able to set up data carrying instances
on compositions of functors, such that different associations carry different instances:
-/

class Foo (F : C ⥤ D) where
  data : Nat

/--
error: failed to synthesize instance of type class
  Foo (F ⋙ G ⋙ H)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (F G H : C ⥤ C) [Foo ((F ⋙ G) ⋙ H)] :
    Foo (F ⋙ (G ⋙ H)) := by
  infer_instance

/-!
With the `[implicit_reducible]` / `[instance_reducible]` split, `[implicit_reducible]`
no longer unfolds during type class synthesis, so the two associations stay distinct here
too — this is the behaviour we want: -/
attribute [local implicit_reducible] Functor.comp in
/--
error: failed to synthesize instance of type class
  Foo (F ⋙ G ⋙ H)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (F G H : C ⥤ C) [Foo ((F ⋙ G) ⋙ H)] :
    Foo (F ⋙ (G ⋙ H)) := by
  infer_instance

/-!
If `Functor.comp` is instance-reducible, the left-associated instance is, undesirably,
synthesized where the right-associated instance is requested. Discrimination keys play no role
here; local instances are always tried. If the instance was global instead of local, Lean would
not even try to apply it because its discrimination key does not match.
-/
attribute [local instance_reducible] Functor.comp in
#guard_msgs in
example (F G H : C ⥤ C) [Foo ((F ⋙ G) ⋙ H)] :
    Foo (F ⋙ (G ⋙ H)) := by
  infer_instance

section

local instance {F G H : C ⥤ C} : Foo ((F ⋙ G) ⋙ H) where data := 0

/-!
If the instance was global instead of local, Lean would not even try to apply it because its
discrimination key does not match.
-/
attribute [local implicit_reducible] Functor.comp in
/--
error: failed to synthesize instance of type class
  Foo (F ⋙ G ⋙ H)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (F G H : C ⥤ C) :
    Foo (F ⋙ (G ⋙ H)) := by
  infer_instance

end
