variables {P : bool → Type} {x : P bool.tt} {y : P bool.ff}

example (b : bool) : P b :=
match b with
| tt := x
| ff := y
end
