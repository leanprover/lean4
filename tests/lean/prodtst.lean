import type

inductive prod (A B : Type₊) :=
mk : A → B → prod A B

set_option pp.universes true
check @prod
