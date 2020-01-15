new_frontend

syntax "<|" term "|>" : term

macro
| `(<| $x |>) => `($x + 1)

#check <| 2 |>

#check <| <| 3 |> |>
