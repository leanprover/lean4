theorem foo : True := trivial

@[deprecated] def Foo.foo : Nat := 3

set_option warningAsError true
set_option linter.all true
open Foo

/--
-/
#guard_msgs in
example : True := foo -- Should not produce warning

/--
error: `Foo.foo` has been deprecated
-/
#guard_msgs in
example : Nat := Foo.foo

namespace Foo

/--
error: `Foo.foo` has been deprecated
-/
#guard_msgs in
example : Nat := foo

end Foo
