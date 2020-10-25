

-- Issue 1
def foo := 10

def f (x : Nat) := x + x

namespace Bla

private def foo := "hello"

#check foo == "world" -- `foo` resolves to private `Bla.foo`

private def foo : Float := 1.0 -- should produce error like in other programming languages

end Bla

#check foo == 0

#check Bla.foo

-- Issue 2
namespace Boo

def boo := 100

namespace Bla

private def boo := "hello"

#check boo == "world" -- resolving to `Boo.Bla.boo` as expected
#check boo ++ "world" -- should work

end Bla

#check Bla.boo == "world"
#check boo == 100

end Boo

#check Boo.Bla.boo == "world"
#check Boo.boo == 100

/-
Should the following work?
```
    namespace N
      private def b := 10
    end N
    open N
    #check b
```
-/

-- Issue 3
private def Nat.mul10 (x : Nat) := x * 10
def x := 10

#check x.mul10 -- dot-notation should work with local private declarations


-- Issue 4

def y := 10
private def y := "hello" -- produce error

private def z := 10
def z := "hello" -- produce error
