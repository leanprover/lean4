constant f : nat → nat → nat
constant g : nat → nat → nat


infix [priority 10] + := f
infix [priority 20] + := g

variables a b : nat

infix [priority std.priority.default+1] + := f
infix + := g
example : a + b = f a b := rfl
infix [priority std.priority.default+2] + := g
example : a + b = g a b := rfl

infix + := f
infix + := g

infix [priority std.priority.default+1] + := g
example : a + b = g a b := rfl
