module
structure Cat (C : Type) where
  hom : C → C → Type
  comp {x y z : C} (f : hom x y) (g : hom y z) : hom x z
  id x : hom x x

structure Foo {C D : Type} (ℭ₁ : Cat C) (ℭ₂ : Cat D) where
  obj : C → D

variable {C D : Type} {ℭ₁ : Cat C} {ℭ₂ : Cat D}

structure Iso (x y : C) where
  hom : ℭ₁.hom x y
  inv : ℭ₁.hom y x
  hom_inv_id : ℭ₁.comp hom inv = ℭ₁.id _
  inv_hom_id : ℭ₁.comp hom inv = ℭ₁.id _

attribute [grind =] Iso.hom_inv_id Iso.inv_hom_id

#guard_msgs in -- Should not produce any issues
set_option trace.grind.issues true in
example (F G : Foo ℭ₁ ℭ₂) (e : ∀ (x : C), Iso (F.obj x) (G.obj x)) (x : C) :
    ℭ₂.comp (e x).hom (e x).inv = ℭ₂.id _ := by
  grind
