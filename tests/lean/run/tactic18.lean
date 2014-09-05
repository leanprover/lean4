import logic
open tactic

variable A : Type.{1}
variable f : A → A → A

theorem tst {a b c : A} (H1 : a = b) (H2 : b = c) : f a b = f b c
:= by apply (@congr A A);
      apply (eq.subst H2);
      apply eq.refl;
      assumption
