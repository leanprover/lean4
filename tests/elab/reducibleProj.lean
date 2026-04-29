/-!
# `@[reducible_proj]` attribute

When a structure projection is tagged `@[reducible_proj]`, `whnfCore` bumps
transparency to `.default` for the structure-argument WHNF if the configured
projection strategy fails to expose a constructor. This lets a `[semireducible]`
definition that produces the structure unfold just enough for the projection to
reduce, without making the whole definition behave as `[implicit_reducible]`
everywhere.
-/

namespace ReducibleProjTest

class Quiver (V : Type) where
  Hom : V → V → Type

infixr:10 " ⟶ " => Quiver.Hom

class Category (obj : Type) extends Quiver obj where
  id : ∀ X : obj, X ⟶ X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

structure Func (C : Type) [Category C] (D : Type) [Category D] where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → (obj X ⟶ obj Y)

infixr:26 " ⥤ " => Func

variable {C D E : Type} [Category C] [Category D] [Category E]

def Func.comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

infixr:80 " ⋙ " => Func.comp

variable (F : C ⥤ D) (G : D ⥤ E)

-- Without the attribute, projection through `Func.comp` fails at `.instances`.
/--
error: Tactic `rfl` failed: The left-hand side
  (F ⋙ G).obj X
is not definitionally equal to the right-hand side
  G.obj (F.obj X)

C D E : Type
inst✝² : Category C
inst✝¹ : Category D
inst✝ : Category E
F : C ⥤ D
G : D ⥤ E
X : C
⊢ (F ⋙ G).obj X = G.obj (F.obj X)
-/
#guard_msgs in
example (X : C) : (F ⋙ G).obj X = G.obj (F.obj X) := by
  with_reducible_and_instances rfl

-- After tagging `Func.obj`, the projection reduces.
attribute [reducible_proj] Func.obj

example (X : C) : (F ⋙ G).obj X = G.obj (F.obj X) := by
  with_reducible_and_instances rfl

-- Tagging `.obj` does not affect `.map`.
/--
error: Tactic `rfl` failed: The left-hand side
  (F ⋙ G).map f
is not definitionally equal to the right-hand side
  G.map (F.map f)

C D E : Type
inst✝² : Category C
inst✝¹ : Category D
inst✝ : Category E
F : C ⥤ D
G : D ⥤ E
X Y : C
f : X ⟶ Y
⊢ (F ⋙ G).map f = G.map (F.map f)
-/
#guard_msgs in
example {X Y : C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f) := by
  with_reducible_and_instances rfl

-- Tagging `.map` too makes that projection reduce as well.
attribute [reducible_proj] Func.map

example {X Y : C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f) := by
  with_reducible_and_instances rfl

end ReducibleProjTest

-- The attribute rejects non-projection functions.
def notAProjection : Nat := 0

/--
error: `@[reducible_proj]` can only be applied to structure projection functions, but `notAProjection` is not one
-/
#guard_msgs in
attribute [reducible_proj] notAProjection
