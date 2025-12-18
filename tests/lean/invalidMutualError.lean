/-! Test invalid mutual block error message -/

inductive Foo : Type where
  | foo0 : Nat → Foo
  | foo1 : Foo → Foo
  | foo2 : Foo → Foo → Foo

mutual

  inductive Bar1 : Foo → Prop where
    | mk {f : Foo} : Bar f → Bar1 (.foo1 f)

  def Bar : Foo → Prop
    | .foo1 f => Bar1 f
    | _ => True

end