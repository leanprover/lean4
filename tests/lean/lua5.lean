Variable x : Int

(**
local N = 100
-- Create N variables with the same type of x
typeofx = env():check_type(Const("x"))
for i = 1, N do
    env():add_var("y_" .. i, typeofx)
end
**)

Show Environment 101
Check x + y_1 + y_2