structure Foo where
  private val : Nat
  name : String

#check { name := "leo", val := 15 : Foo }
#check { name := "leo", val := 15 : Foo }.val
