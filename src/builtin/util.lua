-- Extra useful functions

-- Create sequence of expressions.
-- Examples:
--    local a, b, c = Consts("a,b,c")
-- We can use ';', ' ', ',', tabs ad line breaks for separating the constant names
--    local a, b, c = Consts("a b c")
function Consts(s)
   local r = {}
   local i = 1
   for c in string.gmatch(s, '[^ ,;\t\n]+') do
      r[i] = Const(c)
      i = i + 1
   end
   return unpack(r)
end
