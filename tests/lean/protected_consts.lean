namespace foo
  protected axiom A : Prop
  axiom B : Prop
  protected constant a : foo.A
  constant b : B
  protected axioms (A₁ A₂ : Prop)
  protected constants (a₁ a₂ : foo.A)
  axioms (B₁ B₂ : Prop)
  constants (b₁ b₂ : B)
end foo

open foo
check foo.A
check A  -- error
check foo.a
check a  -- error
check foo.A₁
check foo.A₂
check A₁ -- error
check A₂ -- error
check foo.a₁
check foo.a₂
check a₁ -- error
check a₂ -- error
check foo.B
check B
check foo.b
check b
check foo.b₁
check foo.b₂
check b₁
check b₂
check foo.B₁
check foo.B₂
check B₁
check B₂
