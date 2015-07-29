/-
This example demonstrates why allowing types such as

inductive D : Type :=
| intro : (D → D) → D

would make the system inconsistent
-/

/- If we were allowed to form the inductive type

     inductive D : Type :=
     | intro : (D → D) → D

   we would get the following
-/
universe l
-- The new type A
axiom D : Type.{l}
-- The constructor
axiom introD : (D → D) → D
-- The eliminator
axiom recD   : Π {C : D → Type}, (Π (f : D → D) (r : Π d, C (f d)), C (introD f)) → (Π (d : D), C d)
-- We would also get a computational rule for the eliminator, but we don't need it for deriving the inconsistency.

noncomputable definition id : D → D := λd, d
noncomputable definition v  : D     := introD id

theorem inconsistent : false :=
recD (λ f ih, ih v) v
