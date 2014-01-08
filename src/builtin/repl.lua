-- Simple read-eval-print loop for Lean Lua frontend
local function trim(s)
   return s:gsub('^%s+', ''):gsub('%s+$', '')
end

local function show_results(...)
   if select('#', ...) > 1 then
      print(select(2, ...))
   end
end

print([[Type 'exit' to exit.]])
repeat
   io.write'lean > '
   local s = io.read()
   if s == nil then print(); break end
   if trim(s) == 'exit' then break end
   local f, err = loadstring(s, 'stdin')
   if err then
      f = loadstring('return (' .. s .. ')', 'stdin')
   end
   if f then
      local ok, err = pcall(f)
      if not ok then
         if is_exception(err) then
            print(err:what())
         else
            print(err)
         end
      else
         if err then print(err) end
      end
   else
      print(err)
   end
until false
