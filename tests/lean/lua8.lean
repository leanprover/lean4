Variable x : Int

(**
local env = get_environment()
ty_x = env:check_type(Const("x"))
c = context()
c = context(c, "x", ty_x)
c = context(c, "y", ty_x)
print(c)
o = env:find_object("x")
print(o)
o = env:find_object("y")
print(o)
**)