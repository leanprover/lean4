-- Create a nested lua_State object
S = State()

-- Remarks:
--   '[[ ... ]]' is a multi-line string in Lua
--   obj:method(args) is the syntax for invoking a method
--   it is actually syntax sugar for
--   obj.method(obj, args)
S:dostring([[
   x = 10
]])

-- Variable x is not visible in the main State object
print(x) -- it will print nil
S:dostring([[
   print(x)
]])

-- Remark: '...' is a reference to varargs in Lua
-- We can pass arguments to/from a nested state

-- The following statement passes 10 and 20 as arguments
-- to the nested lua_State object S.
-- The values returned by the script are stored in r1 and r2
r1, r2 = S:dostring([[
   -- extract arguments passed to dostring
   a1, a2 = ...
   return a1 + a2, a1 - a2
]], 10, 20)
print("r1:", r1)
print("r2:", r2)

-- We can communicate integers, strings and Lean objects
f = Const("f")
a = Const("a")
T = S:dostring([[
    t = ...
    g = Const("g")
    return g(g(g(t)))
]], f(a))
print(T)

-- We can also execute commands in a separate thread.
-- The following command creates a thread for running
-- the given script in the state S.
-- It does not wait the thread to finish.
T = thread(S, [[
    t = ...
    g = Const("g")
    b = Const("b")
    return g(b, t)
]], f(a))

-- The method wait makes us wait for the thread T.
-- It return the values returned by the script.
r = T:wait()
-- It will print the Lean expression g(b, f(a))
print(r)
