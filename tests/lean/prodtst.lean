--

inductive prod2 (A B : Type.{_+1})
| mk : A → B → prod2

set_option pp.universes true
#check @prod2
