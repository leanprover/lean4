-- Create a nested lua_State object
S = State()

S:dostring([[
  flag = ...
  print(flag)
]], true)
