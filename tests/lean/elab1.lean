definition foo.subst := @eq.subst
definition boo.subst := @eq.subst

definition foo.add := @add
definition boo.add := @add

set_option pp.all true

open foo boo
#print raw subst -- subst is overloaded
#print raw add   -- add is overloaded

#check @subst

#check @@subst

open eq

#check subst

constants a b : nat
constant H1 : a = b
constant H2 : a + b > 0

#check eq.subst H1 H2
