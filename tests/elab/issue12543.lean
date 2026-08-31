-- Test for issue #12543: `(kernel) declaration has metavariables` when
-- an inductive type index refers to a previous index via `by`.

axiom P : Prop
axiom Q : P → Prop

-- Previously gave: (kernel) declaration has metavariables 'Foo'
inductive Foo : (h : P) → (Q (by exact h)) → Prop

-- These always worked:
inductive Foo' : (h : P) → (Q h) → Prop
inductive Foo'' (h : P) : (Q (by exact h)) → Prop
