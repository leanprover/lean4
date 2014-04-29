env = environment()
env:add_var("N", Type())
env:add_var("x", Const("N"))
for v in env:objects() do
   if v:has_name() then
      print(v:get_name())
   end
end
assert(env:find_object("N"))
assert(not env:find_object("Z"))
assert(env:find_object("N"):is_var_decl())
assert(env:find_object("N"):has_type())
assert(env:find_object("N"):has_name())
assert(env:find_object("N"):get_type() == Type())
assert(env:find_object("N"):get_name() == name("N"))
assert(env:find_object("x"):get_type() == Const("N"))
assert(not env:has_parent())
assert(not env:has_children())
