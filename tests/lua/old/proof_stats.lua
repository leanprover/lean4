parse_lean_cmds([[
variables a b c d e f : Nat
rewrite_set simple
add_rewrite Nat::mul_assoc Nat::mul_comm Nat::mul_left_comm Nat::add_assoc Nat::add_comm Nat::add_left_comm
            Nat::distributer Nat::distributel : simple
]])
local t      = parse_lean("(a + b) * (c + d) * (e + f) * (a + b) * (c + d) * (e + f)")
local t2, pr = simplify(t, "simple")
print(t)
-- Now, we traverse the proof and collect statistics on how often each theorem is used
m = splay_map()
pr:for_each(
        function(e, ctx)
           if e:is_app() and e:arg(0):is_constant() then
              local n = e:arg(0):fields()
              local c = m:find(n)
              if not c then
                 c = 0
              end
              m:insert(n, c+1)
           end
        end)
m:for_each(function(k, v) print(tostring(k) .. " ==> " .. tostring(v)) end)
