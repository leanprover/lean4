/- "Hello world" -/

#eval "hello" ++ " " ++ "world"
-- "hello world"

#check true
-- Bool

def x := 10

#eval x + 2
-- 12

def double (x : Int) := 2*x

#eval double 3
-- 6
#check double
-- Int → Int
example : double 4 = 8 := rfl


