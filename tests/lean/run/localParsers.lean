def f (x y : Nat) := x + 2*y

namespace Foo

local infix:65 (priority := high) "+" => f

theorem ex1 (x y : Nat) : x + y = f x y := rfl

/-- info: 1+2 : Nat -/
#guard_msgs in
#check 1 + 2

end Foo

/-- info: 1 + 2 : Nat -/
#guard_msgs in
#check 1 + 2

theorem ex2 (x y : Nat) : x + y = HAdd.hAdd x y := rfl

open Foo

theorem ex3 (x y : Nat) : x + y = HAdd.hAdd x y := rfl

/-- info: 1 + 2 : Nat -/
#guard_msgs in
#check 1 + 2

section
def g (x y : Nat) := 3*(x+y)

local infix:65 (priority := high) "  +  " => g

theorem ex4 (x y : Nat) : x + y = g x y := rfl

/-- info: 1  + 2 : Nat -/
#guard_msgs in
#check 1 + 2

end

theorem ex5 (x y : Nat) : x + y = HAdd.hAdd x y := rfl

/-- info: 1 + 2 : Nat -/
#guard_msgs in
#check 1 + 2
