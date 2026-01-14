namespace Foo

def x := 10

end Foo

#check Foo.x

open Foo

#check x

theorem ex1 : x = Foo.x := rfl

namespace Foo

def f x y := x + y + 1

scoped infix:70 "~~" => f

#check 1 ~~ 2

theorem ex1 : x ~~ y = f x y := rfl

end Foo

#check 1 ~~ 2 -- works because we have an `open Foo` above

theorem ex2 : x ~~ y = f x y := rfl
theorem ex3 : x ~~ y = Foo.f x y := rfl
