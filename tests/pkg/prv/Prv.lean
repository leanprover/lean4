import Prv.Foo

#check { name := "leo", val := 15 : Foo }
#check { name := "leo", val := 15 : Foo }.name
#check { name := "leo", val := 15 : Foo }.val -- Error
