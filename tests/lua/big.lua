f = Const("f")
a = Const("a")
b = Const("b")
nodes = {}

function mk_big(num)
   local r
   if num == 0 then
      r = f(a, b)
   else
      r = f(mk_big(num-1), mk_big(num-1))
   end
   return r
end

function size(e)
   local r = 0
   e:for_each(function(e, o) assert(e:is_app() or e:is_constant()); r = r + 1 end)
   return r
end

local F = mk_big(14)
print(size(F))
