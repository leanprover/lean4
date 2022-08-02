import UserDeriving.Simple

inductive Foo where
  | mk₁
  | mk₂
  deriving Simple, Inhabited /- Creates `Foo.test`, and then runs builtin handler. -/

example : Foo.test = 0 := by rfl
