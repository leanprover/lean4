
definition f : bool → bool → nat
| _ _ := 10

example : f tt tt = 10 :=
rfl

definition g : bool → bool → bool → nat
| tt _  tt := 1
| _  ff ff := 2
| _  _  _  := 3

example : g tt tt tt = 1 := rfl
example : g tt ff tt = 1 := rfl
example : g tt ff ff = 2 := rfl
example : g ff ff ff = 2 := rfl
example : g ff tt tt = 3 := rfl
