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
