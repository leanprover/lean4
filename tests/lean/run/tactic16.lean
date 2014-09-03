import logic data.string
open tactic

variable A : Type.{1}
variable f : A → A → A

theorem tst {a b c : A} (H1 : a = b) (H2 : b = c) : f a (f b b) = f b (f c c)
:= by discard (apply (subst H1)) 3;  -- discard the first 3 solutions produced by apply
      trace "after subst H1";
      apply (subst H2);
      apply refl
