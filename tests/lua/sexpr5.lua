function display_leaves(s)
   if s:kind() == sexpr_kind.Cons then
      local h, t = s:fields()
      display_leaves(h)
      display_leaves(t)
   else
      print(s)
      assert(s:kind() == sexpr_kind.Nil or s:kind() == sexpr_kind.String or tostring(s:fields()) == tostring(s))
      assert(s:kind() ~= sexpr_kind.String or '"' .. tostring(s:fields()) .. '"' == tostring(s))
   end
end

local l = sexpr(sexpr(1), sexpr(name("a")), sexpr(mpz(10)), sexpr(mpq(3)/2), sexpr(1, 2, 3), sexpr(sexpr("a"), sexpr(10, 2)), sexpr(), sexpr("foo"))
print(l)
display_leaves(l)
