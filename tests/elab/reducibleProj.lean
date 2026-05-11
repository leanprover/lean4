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

-- Regression for the `reduceProj?` path used by `grind` canonicalization (and
-- by `simp`, `cbv`, vcgen, `unfoldProjInst?`). The bump must fire here too, not
-- just in `whnfCore`'s `.proj` arm.
--
-- Without the bump being routed through `reduceProj?`, `grind` cannot discharge
-- naturality below: ematch produces `(F ⋙ H).obj X = H.obj (F.obj X)` but
-- canon collapses both sides without recording the eqc edge, and
-- `NatTrans.naturality` never matches against `(F ⋙ H).map f ≫ β.app _`.

namespace ReducibleProjGrindTest

class Category (obj : Type) : Type 1 where
  Hom : obj → obj → Type
  comp : ∀ {X Y Z : obj}, Hom X Y → Hom Y Z → Hom X Z
  assoc : ∀ {W X Y Z : obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

scoped infixr:10 " ⟶ " => Category.Hom
scoped infixr:80 " ≫ " => Category.comp
attribute [grind _=_] Category.assoc

structure Functor (C : Type) [Category C] (D : Type) [Category D] : Type where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y))
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = map f ≫ map g := by grind

scoped infixr:26 " ⥤ " => Functor

attribute [grind _=_] Functor.map_comp

variable {C : Type} [Category C] {D : Type} [Category D] {E : Type} [Category E]

def Functor.comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

scoped infixr:80 " ⋙ " => Functor.comp

@[grind =]
theorem Functor.comp_obj (F : C ⥤ D) (G : D ⥤ E) (X : C) :
    (F ⋙ G).obj X = G.obj (F.obj X) := rfl

@[grind =]
theorem Functor.comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := rfl

structure NatTrans (F G : C ⥤ D) : Type where
  app (X : C) : F.obj X ⟶ G.obj X
  naturality ⦃X Y : C⦄ (f : X ⟶ Y) :
    F.map f ≫ app Y = app X ≫ G.map f := by grind

attribute [grind _=_] NatTrans.naturality

attribute [reducible_proj] Functor.obj

variable {F G : C ⥤ D}

-- This `grind` call exercises the `Sym.canon` → `reduceProjFn?` → `reduceProj?`
-- chain, which prior to this PR's fix bypassed the `[reducible_proj]` bump.
-- Without the fix, ematch produces `(F ⋙ H).obj _ = H.obj (F.obj _)`
-- equalities but canon collapses them silently, so `NatTrans.naturality` never
-- fires on terms like `(F ⋙ H).map f ≫ β.app (F.obj Y)` and grind fails.
def hcomp {H I : D ⥤ E} (α : NatTrans F G) (β : NatTrans H I) :
    NatTrans (F ⋙ H) (G ⋙ I) where
  app := fun X : C => β.app (F.obj X) ≫ I.map (α.app X)
  naturality := by grind

end ReducibleProjGrindTest

-- The attribute rejects non-projection functions.
def notAProjection : Nat := 0

/--
error: `@[reducible_proj]` can only be applied to structure projection functions, but `notAProjection` is not one
-/
#guard_msgs in
attribute [reducible_proj] notAProjection

-- The attribute rejects class-field projections (they have orthogonal support
-- via `unfoldProjInst?` and `backward.whnf.reducibleClassField`).
class MyClass (α : Type) where
  field : α

/--
error: `@[reducible_proj]` does not apply to class-field projections; mark the underlying instance `[implicit_reducible]` or rely on the existing `unfoldProjInst?` / `backward.whnf.reducibleClassField` mechanism
-/
#guard_msgs in
attribute [reducible_proj] MyClass.field
