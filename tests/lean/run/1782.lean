mutual inductive a, b, c
with a : Type
| foo : a
with b : Type
| bar : b
with c : Type
| baz : c

mutual def f, g, h
with f : a → nat
| a.foo := 0
with g : b → nat
| b.bar := 1
with h : c → nat
| c.baz := 2

example : f a.foo = 0 := rfl
example : g b.bar = 1 := rfl
example : h c.baz = 2 := rfl


mutual def f_1, f_2, f_3, f_4
with f_1 : a → nat
| a.foo := 0
with f_2 : b → nat
| b.bar := 1
with f_3 : c → nat
| c.baz := 2
with f_4 : nat → nat
| 0     := 3
| _     := 4

example : f_1 a.foo = 0 := rfl
example : f_2 b.bar = 1 := rfl
example : f_3 c.baz = 2 := rfl
example : f_4 0 = 3 := rfl
example : f_4 1 = 4 := rfl
