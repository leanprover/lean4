import("util.lua")
local env  = environment()
local ios  = io_state()
local Bool = Const("Bool")
env:add_var("p", Bool)
env:add_var("q", Bool)
local p, q = Consts("p, q")
local ctx  = context()

S = State()
-- Create tactic t1 in a different Lua State.
-- So, t1 can be executed by a different execution
-- thread
local t1 = S:eval([[
     counter1 = 0
     return tactic(function(env, ios, s)
                     while true do
                        print("tactic 1")
                        counter1 = counter1 + 1
                        sleep(10)
                     end
                  end)
]])

counter2 = 0
local t2 = tactic(function(env, ios, s)
                     while true do
                        print("tactic 2")
                        counter2 = counter2 + 1
                        sleep(10)
                     end
                  end)

local T = (t1:par(t2)):try_for(500)
T:solve(env, ios, ctx, p)
assert(counter2 > 2)
S:eval([[ assert(counter1 > 2) ]])
