open num bool

example : le 0 0 = tt := rfl
example : le 0 1 = tt := rfl
example : le 0 2 = tt := rfl
example : le 0 3 = tt := rfl

example : le 1 0 = ff := rfl
example : le 1 1 = tt := rfl
example : le 1 2 = tt := rfl
example : le 1 3 = tt := rfl

example : le 2 0 = ff := rfl
example : le 2 1 = ff := rfl
example : le 2 2 = tt := rfl
example : le 2 3 = tt := rfl
example : le 2 4 = tt := rfl
example : le 2 5 = tt := rfl

example : le 3 0 = ff := rfl
example : le 3 1 = ff := rfl
example : le 3 2 = ff := rfl
example : le 3 3 = tt := rfl
example : le 3 4 = tt := rfl
example : le 3 5 = tt := rfl

example : le 4 0 = ff := rfl
example : le 4 1 = ff := rfl
example : le 4 2 = ff := rfl
example : le 4 3 = ff := rfl
example : le 4 4 = tt := rfl
example : le 4 5 = tt := rfl

example : le 5 0 = ff := rfl
example : le 5 1 = ff := rfl
example : le 5 2 = ff := rfl
example : le 5 3 = ff := rfl
example : le 5 4 = ff := rfl
example : le 5 5 = tt := rfl
example : le 5 6 = tt := rfl

example : 0 - 0 = 0 := rfl
example : 0 - 1 = 0 := rfl
example : 0 - 2 = 0 := rfl
example : 0 - 3 = 0 := rfl

example : 1 - 0 = 1 := rfl
example : 1 - 1 = 0 := rfl
example : 1 - 2 = 0 := rfl
example : 1 - 3 = 0 := rfl

example : 2 - 0 = 2 := rfl
example : 2 - 1 = 1 := rfl
example : 2 - 2 = 0 := rfl
example : 2 - 3 = 0 := rfl
example : 2 - 4 = 0 := rfl

example : 3 - 0 = 3 := rfl
example : 3 - 1 = 2 := rfl
example : 3 - 2 = 1 := rfl
example : 3 - 3 = 0 := rfl
example : 3 - 4 = 0 := rfl
example : 3 - 5 = 0 := rfl

example : 4 - 0 = 4 := rfl
example : 4 - 1 = 3 := rfl
example : 4 - 2 = 2 := rfl
example : 4 - 3 = 1 := rfl
example : 4 - 4 = 0 := rfl
example : 4 - 5 = 0 := rfl

example : 5 - 0 = 5 := rfl
example : 5 - 1 = 4 := rfl
example : 5 - 2 = 3 := rfl
example : 5 - 3 = 2 := rfl
example : 5 - 4 = 1 := rfl
example : 5 - 5 = 0 := rfl

example : 11 - 5 = 6 := rfl
example : 5 - 11 = 0 := rfl
example : 12 - 7 = 5 := rfl
example : 120 - 12 = 108 := rfl
example : 111 - 11 = 100 := rfl
