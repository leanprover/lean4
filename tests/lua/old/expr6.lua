import("util.lua")
function print_leaves(e, ctx)
   if (not e) then
      return
   end
   local k = e:kind()
   if k == expr_kind.Var then
      local i = e:fields()
      local e = ctx:lookup(i)
      print("var idx: " .. i .. ", name: " .. tostring(e:get_name()))
   elseif k == expr_kind.Const then
      local n = e:fields()
      print("constant name: " .. n)
   elseif k == expr_kind.App then
      local num, args = e:fields()
      print("application num args: " .. num)
      for a in args do
         print_leaves(a, ctx)
      end
   elseif k == expr_kind.Lambda or k == expr_kind.Pi then
      local name, domain, body = e:fields()
      print("abstraction var name: " .. tostring(name))
      print_leaves(domain, ctx)
      print_leaves(body, ctx:extend(name, domain))
   elseif k == expr_kind.Let then
      local name, ty, val, body = e:fields()
      print("let var name: " .. tostring(name))
      print_leaves(ty, ctx)
      print_leaves(val, ctx)
      print_leaves(body, ctx:extend(name, ty, val))
   else
      print(e)
   end
end

local f, g, h, a, b, c = Consts("f, g, h, a, b, c")
local N, M    = Consts("N, M")
local x, y, z = Consts("x, y, z")
assert(is_expr(f))

local F = fun(h, mk_arrow(N, N),
              Let(x, h(a), mk_eq(N, f(x), h(x))))
print(F)
print_leaves(F, context())
