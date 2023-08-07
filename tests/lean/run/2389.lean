inductive Foo : Prop → Prop

inductive Bar : Prop
  | bar : Foo Bar → Bar
