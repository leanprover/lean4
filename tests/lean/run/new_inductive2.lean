set_option new_inductive true
universes u v

inductive arrow (α : Type u) (β : Type v)
| mk : (α → β) → arrow

inductive foo
| mk : arrow nat foo → foo

#print foo
#print foo.rec
set_option pp.all true
#print foo.below
