def f (x y : Nat) := x + 2*y

namespace Foo

scoped infix:65 (priority := default+1) "+" => f

theorem ex1 (x y : Nat) : x + y = f x y := rfl

#check 1 + 2

end Foo

#check 1 + 2
theorem ex2 (x y : Nat) : x + y = HAdd.hAdd x y := rfl

open Foo

theorem ex3 (x y : Nat) : x + y = f x y := rfl
#check 1 + 2
