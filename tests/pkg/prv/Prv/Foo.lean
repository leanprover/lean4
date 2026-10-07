private def a := 10

structure Foo where
  private val : Nat
  name : String

#check { name := "leo", val := 15 : Foo }
#check { name := "leo", val := 15 : Foo }.val

structure Name (x : String) where
  private mk ::
  val : String := x
  deriving Repr

inductive Choice where
  | private fst (n : Nat)
  | private snd (n : Nat)

inductive Mixed where
  | private hidden (n : Nat)
  | shown (n : Nat)

example : Name "hello" := by constructor; exact "hello"
example : Choice := by left; exact 0
