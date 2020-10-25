

namespace Foo

syntax[foo] "bla!" term : term

macro_rules[foo]
| `(bla! $x) => pure x

#check bla! 10

end Foo
