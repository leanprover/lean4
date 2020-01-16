new_frontend

syntax term "+++":60 term:59 : term

syntax "<|" term "|>" : term

macro
| `($a +++ $b) => `($a + $b + $b)

macro
| `(<| $x |>) => `($x +++ 1)

#check <| 2 |>

#check <| <| 3 |> |>
