function display_token_table(s)
   s:for_each(function(k, cmd, val, prec)
                 io.write(k)
                 if cmd then
                    io.write(" [command]")
                 end
                 print(" => " .. tostring(val) .. " " .. tostring(prec))
   end)
end

function token_table_size(s)
   local r = 0
   s:for_each(function() r = r + 1 end)
   return r
end

local s = token_table()
assert(is_token_table(s))
assert(token_table_size(s) == 0)
s = s:add_command_token("test",  "tst1")
s = s:add_command_token("tast",  "tst2")
s = s:add_command_token("tests", "tst3")
s = s:add_command_token("fests", "tst4")
s = s:add_command_token("tes",   "tst5")
s = s:add_token("**", "**", 65)
s = s:add_token("**-", "ttimeminus")
assert(token_table_size(s) == 7)
display_token_table(s)


print("========")
local s2 = default_token_table()
display_token_table(s2)
assert(token_table_size(s2) > 0)
local sz1 = token_table_size(s)
local sz2 = token_table_size(s2)
s2 = s2:merge(s)
assert(token_table_size(s2) == sz1 + sz2)
s2 = s2:find("t"):find("e")
print("========")
display_token_table(s2)
assert(token_table_size(s2) == 3)
s2 = s2:find("s")
local cmd, val, prec = s2:value_of()
assert(val == name("tst5"))
