constant f : nat → nat → nat
constant g : nat → nat → nat


infix [priority 10] + := f
infix [priority 20] + := g

variables a b : nat

example : a + b = g a b := rfl
infix [priority 5] + := g
example : a + b = f a b := rfl
infix [priority 15] + := g
example : a + b = g a b := rfl

infix [priority default+1] + := f
infix + := g
example : a + b = f a b := rfl
infix [priority default+2] + := g
example : a + b = g a b := rfl

infix + := f
infix + := g
example : a + b = f a b := rfl

infix [priority default+1] + := g
example : a + b = g a b := rfl
