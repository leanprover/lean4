open num bool

example : num.le 0 0 = tt := rfl
example : num.le 0 1 = tt := rfl
example : num.le 0 2 = tt := rfl
example : num.le 0 3 = tt := rfl

example : num.le 1 0 = ff := rfl
example : num.le 1 1 = tt := rfl
example : num.le 1 2 = tt := rfl
example : num.le 1 3 = tt := rfl

example : num.le 2 0 = ff := rfl
example : num.le 2 1 = ff := rfl
example : num.le 2 2 = tt := rfl
example : num.le 2 3 = tt := rfl
example : num.le 2 4 = tt := rfl
example : num.le 2 5 = tt := rfl

example : num.le 3 0 = ff := rfl
example : num.le 3 1 = ff := rfl
example : num.le 3 2 = ff := rfl
example : num.le 3 3 = tt := rfl
example : num.le 3 4 = tt := rfl
example : num.le 3 5 = tt := rfl

example : num.le 4 0 = ff := rfl
example : num.le 4 1 = ff := rfl
example : num.le 4 2 = ff := rfl
example : num.le 4 3 = ff := rfl
example : num.le 4 4 = tt := rfl
example : num.le 4 5 = tt := rfl

example : num.le 5 0 = ff := rfl
example : num.le 5 1 = ff := rfl
example : num.le 5 2 = ff := rfl
example : num.le 5 3 = ff := rfl
example : num.le 5 4 = ff := rfl
example : num.le 5 5 = tt := rfl
example : num.le 5 6 = tt := rfl

example : num.sub 0 0 = 0 := rfl
example : num.sub 0 1 = 0 := rfl
example : num.sub 0 2 = 0 := rfl
example : num.sub 0 3 = 0 := rfl

example : num.sub 1 0 = 1 := rfl
example : num.sub 1 1 = 0 := rfl
example : num.sub 1 2 = 0 := rfl
example : num.sub 1 3 = 0 := rfl

example : num.sub 2 0 = 2 := rfl
example : num.sub 2 1 = 1 := rfl
example : num.sub 2 2 = 0 := rfl
example : num.sub 2 3 = 0 := rfl
example : num.sub 2 4 = 0 := rfl

example : num.sub 3 0 = 3 := rfl
example : num.sub 3 1 = 2 := rfl
example : num.sub 3 2 = 1 := rfl
example : num.sub 3 3 = 0 := rfl
example : num.sub 3 4 = 0 := rfl
example : num.sub 3 5 = 0 := rfl

example : num.sub 4 0 = 4 := rfl
example : num.sub 4 1 = 3 := rfl
example : num.sub 4 2 = 2 := rfl
example : num.sub 4 3 = 1 := rfl
example : num.sub 4 4 = 0 := rfl
example : num.sub 4 5 = 0 := rfl

example : num.sub 5 0 = 5 := rfl
example : num.sub 5 1 = 4 := rfl
example : num.sub 5 2 = 3 := rfl
example : num.sub 5 3 = 2 := rfl
example : num.sub 5 4 = 1 := rfl
example : num.sub 5 5 = 0 := rfl

example : num.sub 11 5 = 6 := rfl
example : num.sub 5 11 = 0 := rfl
example : num.sub 12 7 = 5 := rfl
example : num.sub 120 12 = 108 := rfl
example : num.sub 111 11 = 100 := rfl
