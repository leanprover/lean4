definition foo.subst := @eq.subst
definition boo.subst := @eq.subst

definition foo.add := @add
definition boo.add := @add

set_option pp.all true

open foo boo
print raw subst -- subst is overloaded
print raw add   -- add is overloaded

#elab @subst

#elab @@subst

#elab subst

#elab add

constants a b : nat
constant H1 : a = b
constant H2 : a + b > 0

#elab eq.subst H1 H2
