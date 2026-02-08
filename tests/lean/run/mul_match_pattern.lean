namespace mul_match_pattern

inductive Foo
  | x
  | bar (y z : Foo)

instance : Mul Foo where
  mul := Foo.bar

def quux : Foo → Foo
  | .x => .x
  | y * _z => y

end mul_match_pattern
