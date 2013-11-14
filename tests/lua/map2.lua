local m = splay_map()
for i = 1, 100 do
   m:insert(i, i * 3)
end

local prev_k = nil
-- It is safe to add/erase elements from m while we are traversing.
-- The for_each method will traverse the elements that are in m
-- when the for_each is invoked
m:for_each(
   function(k, v)
      if prev_k then
         assert(prev_k < k)
      end
      print(k .. " -> " .. v)
      prev_k = k
      m:insert(-k, v)
   end
)

assert(m:size() == 200)
m2 = m:copy()
m:for_each(
   function(k, v)
      assert(m2:contains(-k))
      assert(m2:find(-k) == v)
      if k > 0 then
         m:erase(k)
      end
   end
)
assert(m:size() == 100)
m:for_each(function(k, v) assert(k < 0) end)
