-- Test for inductive type index using another via `by`
axiom P : Prop
axiom Q : P → Prop

-- This should work: an inductive type index uses another through a tactic (a `by` block)
inductive Foo : (h : P) → (Q (by exact h)) → Prop

-- This works: without `by`
inductive Foo' : (h : P) → (Q h) → Prop

-- This works: when first index is a parameter
inductive Foo'' (h : P) : (Q (by exact h)) → Prop
