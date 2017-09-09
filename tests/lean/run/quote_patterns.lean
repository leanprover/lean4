meta def f : expr → option (expr × expr × expr)
| `(%%x = %%c*%%y) := some (x, c, y)
| _ := none

meta def g : expr → nat
| `(%%x = 0) := 2
| _ := 0
