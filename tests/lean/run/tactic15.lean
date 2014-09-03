import logic
open tactic

variable A : Type.{1}
variable f : A → A → A

theorem tst {a b c : A} (H1 : a = b) (H2 : b = c) : f a (f b b) = f b (f c c)
:= by apply (subst H1);
      trace "trying again... ";
      state;
      apply (subst H2);
      apply refl
