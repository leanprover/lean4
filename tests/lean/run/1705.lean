import data.stream

inductive T : Type
| mk : nat → T

notation `&-` := T.mk

example : T → T
| (&- x) := &- x --works

notation `&-` := list.head

example : T → T
| (&- x) := &- x

def f {α} : list α → nat
| []      := 0
| (a::as) := f as + 1
