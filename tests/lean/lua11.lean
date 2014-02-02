import Int.
(*

 local env = get_environment()
 local o1  = env:find_object(name("Int", "add"))
 print(o1:get_value())
 assert(is_kernel_object(o1))
 assert(o1)
 assert(o1:is_builtin())
 assert(o1:keyword() == "builtin")
 assert(o1:get_name() == name("Int", "add"))
 local o2  = env:find_object("xyz31213")
 assert(not o2)

 local found1 = false
 local found2 = false
 local bs = nil
 for obj in env:objects() do
    if not obj:has_name() then
       found1 = true
    end
    if obj:is_builtin_set() then
       if not found2 then
          found2 = true
          bs = obj
       end
    end
 end
 assert(found1)
 assert(found2)
 print(bs)
 assert(not bs:in_builtin_set(Const("a")))

 assert(not pcall(function() o1:get_cnstr_level() end))
 env:add_var("x", Const("Int"))
 env:add_definition("val", Const("Int"), Const("x"))
 assert(env:find_object("val"):get_value() == Const("x"))
 assert(env:find_object("val"):get_weight() == 1)
 assert(env:find_object("congr"):is_opaque())
 assert(env:find_object("congr"):is_theorem())
 assert(env:find_object("hrefl"):is_axiom())
 assert(env:find_object(name("Int", "sub")):is_definition())
 assert(env:find_object("x"):is_var_decl())
*)
