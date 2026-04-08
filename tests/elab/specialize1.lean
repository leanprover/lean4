example (x y z : Prop) (f : x → y → z) (xp : x) (yp : y) : z := by
  specialize f xp yp
  assumption

example (B C : Prop) (f : forall (A : Prop), A → C) (x : B) : C := by
  specialize f _ x
  exact f

example (B C : Prop) (f : forall {A : Prop}, A → C) (x : B) : C := by
  specialize f x
  exact f

example (B C : Prop) (f : forall {A : Prop}, A → C) (x : B) : C := by
  specialize @f _ x
  exact f

example (X : Type) [Add X] (f : forall {A : Type} [Add A], A → A → A) (x : X) : X := by
  specialize f x x
  assumption

def ex (f : Nat → Nat → Nat) : Nat := by
  specialize f _ _
  exact 10
  exact 2
  exact f

example : ex (· - ·) = 8 :=
  rfl
