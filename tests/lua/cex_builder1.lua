local cex = cex_builder(function(n, cex, a)
                          if cex then
                             return cex
                          else
                             error("no counterexample")
                          end
end)
assert(is_cex_builder(cex))
local env = environment()
env:add_var("T", Type())
local a   = assignment()
local env2 = cex("main", env, a)
assert(env2:find_object("T"))
assert(not pcall(function() cex("main", nil, a) end))
