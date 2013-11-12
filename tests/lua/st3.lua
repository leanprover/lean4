S = State()
function mk(x)
   return function (y)
             return x * y
          end
end
f = mk(20)
S:eval([[
g, x = ...
print("x", x)
print(g(10))
]], f, 10)

function mkcounter()
   local x = 0
   function inc()
      x = x + 1
      return x
   end
   function dec()
      x = x - 1
      return x
   end
   return inc, dec
end

inc1, dec1 = mkcounter()
print(inc1())
print(inc1())
print(dec1())
print(inc1())
print(inc1())
-- inc1 and dec1 are closures, they share the same upvalue x.
-- However, when we copy inc1 and dec1 to S, we get two copies of x.
S:eval([[
  inc2, dec2, x = ...
  print("in the nested state")
  print("x", x)
  print("incrementing", inc2())
  print("incrementing", inc2())
  print("decrementing", dec2())
]], inc1, dec1, 10)
print(inc1())

S:set("h", f)
print(S:eval([[ return h(2) ]]))
