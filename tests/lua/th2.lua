S = State()
T = thread(S, [[
  while true do
     check_interrupted()
  end
]])

sleep(100)
T:interrupt()
assert(not pcall(function() T:wait() end))
