/-!
# Test verifying that nested predicates don't trigger the generation of `below` lemmas
Since the case of nested predicates is not currently handled by `mkBelow`,
trying to generate `Bar.below` triggers an error upon defining the inductive type.
-/

inductive Foo : Prop → Prop

inductive Bar : Prop
  | bar : Foo Bar → Bar
