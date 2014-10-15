import logic
open tactic

constant A : Type.{1}
constant f : A → A → A

theorem tst {a b c : A} (H1 : a = b) (H2 : b = c) : f a b = f b c
:= by apply (eq.subst H1);
      apply (eq.subst H2);
      apply eq.refl
