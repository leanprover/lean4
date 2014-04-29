import("util.lua")
-- This examples demonstrates that Lean objects are not very useful as Lua table keys.
local f = Const("f")
local m = {}
local env = environment()
env:add_var("T", Type())
env:add_var("f", mk_arrow(Const("T"), Const("T")))
for i = 1, 100 do
   env:add_var("a" .. i, Const("T"))
   local t = f(Const("a" .. i))
   -- Any object can be a key of a Lua table.
   -- But, Lua does not use the method __eq for comparing keys.
   -- The problem is that Lua uses its own hashcode that may not
   -- be compatible with the __eq implemantion.
   -- By non-compatible, we mean two objects my be equal by __eq, but
   -- the hashcodes may be different.
   m[t] = i
end

for t1, i in pairs(m) do
   local t2 = f(Const("a" .. i))
   -- print(t1, i, t2)
   assert(m[t1] == i)
   -- t1 and t2 are structurally equal
   assert(t1 == t2)
   -- t1 and t2 are different objects
   assert(not t1:is_eqp(t2))
   -- t2 is not a key of map
   assert(m[t2] == nil)
   assert(env:normalize(t1) == t1)
   assert(t1:instantiate(Const("a")) == t1)
   local t1_prime = t1:instantiate(Const("a"))
   -- t1 and t1_prime are structurally equal
   assert(t1 == t1_prime)
   -- Moreover, they are references to the same Lean object
   assert(t1:is_eqp(t1_prime))
   -- But, they are wrapped by different Lua userdata
   assert(m[t1_prime] == nil)
end

-- We can store elements that implement __lt and __eq metamethods in splay_maps.
-- The implementation assumes that the elements stored in the splay map can be totally ordered by __lt
m = splay_map()
m:insert(Const("a"), 10)
assert(m:contains(Const("a")))
assert(not m:contains(Const("b")))
assert(m:find(Const("a")) == 10)
local a, b = Consts("a, b")
m:insert(f(a, b), 20)
assert(m:find(f(a, b)) == 20)
assert(m:find(f(a, a)) == nil)
assert(m:size() == 2)
assert(#m == 2)
m:erase(f(a, a))
assert(m:size() == 2)
m:erase(f(a, b))
assert(m:size() == 1)
for i = 1, 100 do
   local t = f(Const("a" .. i))
   m:insert(t, i)
   assert(m:contains(t))
   assert(m:find(t) == i)
end

assert(m:size() == 101)

for i = 1, 100 do
   local t = f(Const("a" .. i))
   assert(m:find(t) == i)
end

-- The following call fails because integers cannot be compared with Lean expressions
assert(not pcall(function() m:insert(10, 20) end))

-- Splay maps copy operation is O(1)
local m2 = m:copy()
m2:insert(b, 20)
assert(m:size() == 101)
assert(m2:size() == 102)

-- We can also traverse all elements in the map
local num = 0
m:for_each(
   function(k, v)
      print(tostring(k) .. " -> " .. v)
      num = num + 1
   end
)
assert(num == 101)
