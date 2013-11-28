local env  = environment()
local ios  = io_state()
local Bool = Const("Bool")
env:add_var("p", Bool)
env:add_var("q", Bool)
local p, q = Consts("p, q")
local ctx  = context()

S = State()
-- tactics t1 and t2 uses yield to implement cooperative
-- multitasking
local counter1 = 0
local t1 = tactic(function(env, ios, s)
                     while true do
                        counter1 = counter1 + 1
                        coroutine.yield()
                     end
end)

local counter2 = 0
local t2 = tactic(function(env, ios, s)
                     while true do
                        counter2 = counter2 + 1
                        coroutine.yield()
                     end
                  end)

local T = (t1:par(t2)):try_for(150)
T:solve(env, ios, ctx, p)
print(counter1, counter2)
assert(counter1 > 2)
assert(counter2 > 2)
