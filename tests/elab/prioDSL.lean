macro "foo!" x:term:max : term => `($x - 1)

theorem ex1 : foo! 10 = 9 := rfl

macro (priority := high) "foo! " x:term:max : term => `($x + 1)

theorem ex2 : foo! 10 = 11 := rfl

macro (priority := low) "foo! " x:term:max : term => `($x * 2)

theorem ex3 : foo! 10 = 11 := rfl

macro (priority := high+1) "foo! " x:term:max : term => `($x * 2)

theorem ex4 : foo! 10 = 20 := rfl

macro (priority := high+4-2) "foo! " x:term:max : term => `($x * 3)

theorem ex5 : foo! 10 = 30 := rfl
