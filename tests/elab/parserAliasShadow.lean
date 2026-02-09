namespace Foo
-- The following declaration shadows the builtin parser alias `letDecl`
syntax letDecl := term ">==>" term

syntax "foo!" letDecl : term

macro_rules
  | `(foo! $x:term >==> $y) => `($x + $y)

end Foo

-- The following declaration shadows the builtin parser alias `letDecl`
syntax letDecl := term ">=>=>" term

syntax "bla!" letDecl : term

macro_rules
  | `(bla! $x:term >=>=> $y) => `($x * $y)

syntax "boo!" Foo.letDecl : term

macro_rules
  | `(boo! $x:term >==> $y) => `($x - $y)

theorem ex1 : (foo! 10 >==> 20) = 30   := rfl
theorem ex2 : (bla! 10 >=>=> 20) = 200 := rfl
theorem ex3 : (boo! 30 >==> 20) = 10   := rfl
