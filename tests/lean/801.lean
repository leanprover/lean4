syntax "a" num : term

macro_rules
  | `(a 0) => `("zero")
  | `(a 1) => `("one")

#check a 1

syntax "b" str : term

macro_rules
  | `(b "foo") => `("foo!")
  | `(b "bla") => `("bla!")

#check b "bla"
