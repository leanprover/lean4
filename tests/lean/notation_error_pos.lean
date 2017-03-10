notation `foo` := "a" + 1
notation `bla` a := a + 1
notation `boo` a := 1 + a
notation `cmd` a := λ x, x + a

#check foo

#check bla "a"

#check boo "a"

#check cmd "b"
