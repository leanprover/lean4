

def Bla.x := 10

namespace Foo
export Bla(x)
end Foo

open Foo
/-- info: Bla.x : Nat -/
#guard_msgs in
#check x
