constants  a b  : nat
constant  p     : nat → Prop
constant  H1    : p (a + a + a)
constant  H2    : a = b
#check (eq.subst H2 H1 : p (a + b + a))
