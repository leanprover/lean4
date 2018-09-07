universes u v

inductive arrow (α : Type u) (β : Type v)
| mk : (α → β) → arrow

inductive foo
| mk : arrow nat foo → foo

#print foo
#print foo.rec
set_option pp.all true
#print foo.below

mutual inductive foo2, arrow2
with foo2 : Type
| mk : arrow2 → foo2
with arrow2 : Type
| mk : (nat → foo2) → arrow2

#print foo2.brec_on
