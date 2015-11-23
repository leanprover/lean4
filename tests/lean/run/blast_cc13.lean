set_option blast.subst false
set_option blast.simp  false
set_option blast.init_depth 10
set_option blast.inc_depth  100

example (p : nat → nat → Prop) (f : nat → nat) (a b c d : nat) :
        p (f a) (f b) → a = c → b = d → b = c → p (f c) (f c) :=
by blast

example (p : nat → nat → Prop) (a b c d : nat) :
        p a b → a = c → b = d → p c d :=
by blast

example (p : nat → nat → Prop) (f : nat → nat) (a b c d : nat) :
        p (f (f (f (f (f (f a))))))
          (f (f (f (f (f (f b)))))) →
        a = c → b = d → b = c →
        p (f (f (f (f (f (f c))))))
          (f (f (f (f (f (f c)))))) :=
by blast
