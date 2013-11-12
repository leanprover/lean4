S1 = State()
S2 = State()
code = [[
   id = ...
   for i = 1, 10000 do
       print("id: " .. id .. ", val: " .. i)
   end
]]
T1 = thread(S1, code, 1)
T2 = thread(S2, code, 2)
T1:wait()
T2:wait()
