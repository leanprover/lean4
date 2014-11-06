import logic

inductive acc1 (A : Type) (R : A → A → Prop) (a : A) :  Prop :=
intro : ∀ (x : A), (∀ (y : A), R y x → acc1 A R y) → acc1 A R x

section

  variables (A : Type) (R : A → A → Prop)

  inductive acc2 (a : A) : Prop :=
  intro : ∀ (x : A), (∀ (y : A), R y x → acc2 y) → acc2 x

end

print "done"
