syntax foo := "a" <|> "b"

syntax "bla" foo : term -- TODO: necessary to declare a and b as keywords

#check `(foo| a)
#check (· matches `(foo| a))
