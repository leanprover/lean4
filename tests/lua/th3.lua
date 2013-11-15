S = State()
T = thread(S, [[
    print("starting thread...")
    pcall(function()
       while true do
          check_interrupted()      -- check if thread was interrupted
          local ok, val = read(10) -- 10 ms timeout
          if ok then
            print("thread received:", val)
            write(val + 10, val - 10) -- send result back to main thread
          end
       end
    end)
]])

for i = 1, 10 do
   T:write(10 * i)
   local r1 = T:read()
   local r2 = T:read()
   print("main received: ", r1, r2)
end
T:interrupt()
print("done")

-- Channels are quite flexible, we can send closure over the channel
T = thread(S, [[
for i = 1, 10 do
   local f = read()
   -- send back the result of f(i)
   write(f(i))
end
]])

for i = 1, 10 do
   T:write(function (x) return x + i end)
   print(T:read())
end
