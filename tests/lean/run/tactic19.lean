import logic
open tactic

theorem tst {A : Type} {f : A → A → A} {a b c : A} (H1 : a = b) (H2 : b = c) : f a b = f b c
:= by apply congr;
      apply (subst H2);
      apply eq.refl;
      assumption
