structure {u} foo : Type (u+2) :=
(elim : Type u → Type u)

set_option pp.universes true
#check foo.elim
#check foo
