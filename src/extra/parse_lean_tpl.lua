-- Parse a template expression string 'str'.
-- The string 'str' contains placeholders of the form 'a::i', where 'i' is a numeral.
-- The placeholders are replaced with values from the array 'args'.
-- See 'test' function for an example.
function parse_lean_tpl(str, args, env, opts, fmt)
   assert(type(str) == "string")
   assert(type(args) == "table")
   assert(env == nil or is_environment(env))
   if #args == 0 then
      return parse_lean(str, env, opts, fmt)
   else
      -- Create the string "fun (a::1 : type-of-args[1]) ... (a::n : type-of-args[n]), $str",
      -- where n is the size of args
      local inferer = type_inferer(env)
      local tbl = {"fun"}
      for i = 1, #args do
         table.insert(tbl, " (a::")
         table.insert(tbl, i)
         table.insert(tbl, " : ")
         table.insert(tbl, tostring(inferer(args[i])))
         table.insert(tbl, ")")
      end
      table.insert(tbl, ", ")
      table.insert(tbl, str)
      local new_str = table.concat(tbl)
      local r = parse_lean(new_str, env, opts, fmt)
      for i = 1, #args do
         assert(r:is_lambda())
         local n, d, body = r:fields()
         r = body:instantiate(args[i])
      end
      return r
   end
end

local test = function()
   local env  = environment()
   -- Load environment with some definitions
   parse_lean_cmds([[
        Variables a b : Real
        Variable  f : Real -> Real
        Variable  g : Real -> Real -> Real
]], env)
   local a, b, g = Consts("a, b, g")
   local t1      = parse_lean_tpl("a::1 + (f a::2) - 10 + a::2", {a, g(b, a)}, env)
   print(t1)
   local t2      = parse_lean_tpl("f (a::1 + 1)", {g(b, b)}, env)
   print(t2)
end

if not pcall(debug.getlocal, 4, 1) then
   -- Main file
   test()
end
