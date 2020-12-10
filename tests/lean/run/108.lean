macro "m" n:ident : command => `(def $n := 1)

m foo

#check foo
