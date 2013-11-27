
S = State()
T = thread(S, [[
   sleep(10000)
]])

T:interrupt()
local ok, msg = pcall(function() T:wait() end)
assert(not ok)
assert(is_exception(msg))
assert(msg:what() == "interrupted")
