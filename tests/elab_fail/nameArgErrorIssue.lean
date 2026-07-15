def boo (x : Nat) (y : Nat) := x + y
def bla (x : Nat) := boo x

#check bla (y := 2) 5     -- Ok
#check bla (y := 5) "hi"  -- 1 error at "hi"
#check bla (z := 5) "hi"  -- 2 errors at `(z := 5)` and "hi"
#check bla (z := 5) 2     -- 1 errors at `(z := 5)`
