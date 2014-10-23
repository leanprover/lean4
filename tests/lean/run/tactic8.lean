import logic
open tactic

theorem tst {A B : Prop} (H1 : A) (H2 : B) : A ∧ B ∧ A :=
by apply @and.intro;
   apply (show A, from H1);
   apply (show B ∧ A, from and.intro H2 H1)

check @tst
