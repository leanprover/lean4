inductive {u} one1 : Type u
| unit : one1

inductive pone : Type 0
| unit : pone

inductive {u} two : Type (max 1 u)
| o : two
| u : two

inductive {u} wrap : Type (max 1 u)
| mk : true → wrap

inductive {u} wrap2 (A : Type u) : Type (max 1 u)
| mk : A → wrap2

set_option pp.universes true
#check @one1.rec
#check @pone.rec
#check @two.rec
#check @wrap.rec
#check @wrap2.rec
