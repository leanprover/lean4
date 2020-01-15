new_frontend

syntax "<|" term "|>" : term

macro
| `(<| $x |>) => `($x + 1)

#check <| 1 |>

#check <| <| 1 |> |>
