universes u v

inductive arrow (α : Type u) (β : Type v)
| mk : (α → β) → arrow

inductive foo
| mk : arrow Nat foo → foo

#print foo
#print foo.rec
setOption pp.all True
#print foo.below

mutual inductive foo2, arrow2
with foo2 : Type
| mk : arrow2 → foo2
with arrow2 : Type
| mk : (Nat → foo2) → arrow2

#print foo2.brecOn
