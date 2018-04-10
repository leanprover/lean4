set_option pp.implicit true

#check (λ a b : nat, (nat.rec_on a (λ b, b) (λ a' ih b, ih b + 1) b : nat))

#check (λ a b : nat, (nat.rec_on a (λ b, b) (λ a' ih b, ih b + 1) b : nat))

constants a b c : nat
constant  p     : nat → nat → Prop
constant  f     : nat → nat
axiom     H1    : p (f a) (f a)
axiom     H2    : a = b
axiom     H3    : a = c

#check (eq.subst H2 H1 : p (f a) (f b))
#check (eq.subst H2 (eq.subst H3 H1) : p (f c) (f b))

axiom     H4    : a + 1 = b
axiom     H5    : p (a + nat.succ nat.zero) a
#check (eq.subst H4 H5 : p b a)
