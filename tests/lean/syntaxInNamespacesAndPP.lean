namespace Foo

syntax "foo" term : term

macro_rules
  | `(foo $x) => x

set_option trace.Elab true in
#check foo true

end Foo

namespace Bla

syntax (name := bla) "bla" term : term

macro_rules
  | `(bla $x) => x

set_option trace.Elab true in
#check bla true

#print Bla.bla

end Bla
