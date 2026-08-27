
@[reducible] 
syntax (name := fooParser) "foo" term : term

#print fooParser

macro_rules
  | `(foo $x) => `($x + 1)

#check foo 5

