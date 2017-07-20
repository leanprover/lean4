def {u} stream (α : Type u) := nat → α
constant stream.cons {α} (a : α) (s : stream α) : stream α
notation h :: t := stream.cons h t

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
