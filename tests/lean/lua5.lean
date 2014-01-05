Import Int.
Variable x : Int

(*
local N   = 100
local env = get_environment()
-- Create N variables with the same type of x
typeofx = env:type_check(Const("x"))
for i = 1, N do
    env:add_var("y_" .. i, typeofx)
end
*)

print Environment 101
Check x + y_1 + y_2