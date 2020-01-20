new_frontend

notation a `**`:50 b:50 => b * a * b
notation "~" a => a+a
namespace Foo
notation "~~" a => a+a
end Foo

syntax term "+++":60 term:59 : term

syntax "<|" term "|>" : term

macro_rules
| `($a +++ $b) => `($a + $b + $b)

macro_rules
| `(<| $x |>) => `($x +++ 1 ** 2)


#check <| 2 |>

#check <| ~2 |>

#check <| <| 3 |> |>
