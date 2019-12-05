-- Issue 1
def foo := 10

def f (x : Nat) := x + x

namespace Bla

private def foo := "hello"

#check foo -- error: ambiguous overload. It should resolve to `Bla.foo`

end Bla

-- Issue 2
namespace Boo

def boo := 100

namespace Bla

private def boo := "hello"

#check boo -- resolving to `Boo.boo` instead of `Boo.Bla.boo`

#check boo ++ "world" -- error since it is resolving to `Boo.Bla.boo`

end Bla

end Boo

-- Issue 3
private def Nat.mul10 (x : Nat) := x * 10
def x := 10

#eval x.mul10 -- error, field notation does not work for private definitions
