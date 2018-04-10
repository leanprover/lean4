open tactic

example (a b : nat) : (a = b ↔ a = b) :=
by cc

example (a b : nat) : (a = b) = (b = a) :=
by cc

example (a b : nat) : (a = b) == (b = a) :=
by cc

example (p : nat → nat → Prop) (f : nat → nat) (a b c d : nat) :
        p (f a) (f b) → a = c → b = d → b = c → p (f c) (f c) :=
by cc

example (p : nat → nat → Prop) (a b c d : nat) :
        p a b → a = c → b = d → p c d :=
by cc

example (p : nat → nat → Prop) (f : nat → nat) (a b c d : nat) :
        p (f (f (f (f (f (f a))))))
          (f (f (f (f (f (f b)))))) →
        a = c → b = d → b = c →
        p (f (f (f (f (f (f c))))))
          (f (f (f (f (f (f c)))))) :=
by cc

constant R : nat → nat → Prop

example (a b c : nat) : a = b → R a b → R a a :=
by cc

example (a b c : Prop) : a = b → b = c → (a ↔ c) :=
by cc

example (a b c : Prop) : a = b → b == c → (a ↔ c) :=
by cc

example (a b c : nat) : a == b → b = c → a == c :=
by cc

example (a b c : nat) : a == b → b = c → a = c :=
by cc

example (a b c d : nat) : a == b → b == c → c == d → a = d :=
by cc

example (a b c d : nat) : a == b → b = c → c == d → a = d :=
by cc

example (a b c : Prop) : a = b → b = c → (a ↔ c) :=
by cc

example (a b c : Prop) : a == b → b = c → (a ↔ c) :=
by cc

example (a b c d : Prop) : a == b → b == c → c == d → (a ↔ d) :=
by cc

definition foo (a b c d : Prop) : a == b → b = c → c == d → (a ↔ d) :=
by cc

example (a b c : nat) (f : nat → nat) : a == b → b = c → f a == f c :=
by cc

example (a b c : nat) (f : nat → nat) : a == b → b = c → f a = f c :=
by cc

example (a b c d : nat) (f : nat → nat) : a == b → b = c → c == f d → f a = f (f d) :=
by cc
