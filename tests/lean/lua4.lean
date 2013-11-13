Variable x : Int

(**
-- Add a variable to the environment using Lua
-- The type of the new variable is equal to the type
-- of x
local env = get_environment()
typeofx = env:check_type(Const("x"))
print("type of x is " .. tostring(typeofx))
env:add_var("y", typeofx)
**)

Check x + y
