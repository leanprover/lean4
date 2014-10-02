import logic
open tactic

constant A : Type.{1}
constant f : A → A → A
open eq
theorem tst {a b c : A} (H1 : a = b) (H2 : b = c) : f a (f b b) = f b (f c c)
:= by apply (subst H1);
      trace "trying again... ";
      state;
      apply (subst H2);
      apply eq.refl
