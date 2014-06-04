-- Given a term t that does not contain global universe levels,
-- This procedure produces a new environment based on env, but
-- without using universe polymorphism. The optional argument
-- def_level is used to instantiate global universe levels used
-- in the definitions t depends on.
function elim_univ_poly(env, t, def_level)
   if not def_level then
      -- If def_level is not provided, set it to universe 1.
      def_level = level()+1
   end

   -- Create the new environment
   local new_env = environment()
   -- Already processed definitions
   local map     = rb_map()

   -- TODO(Leo): convert inductive datatypes.

   -- Return a new (based on n) that is not used in new_env
   function mk_name(n)
      local i = 1
      local r = n
      while new_env:find(r) do
         r = name(n, i)
         i = i + 1
      end
      return r
   end

   -- Instantiate the declaration decl from env using the levels ls,
   -- and add it to new_env. Return the name of this instance in new_env.
   function process_declaration(decl, ls)
      local new_name = mk_name(decl:name())
      local ps       = decl:univ_params()
      local new_type = process_expr(decl:type(), ps, ls)
      local new_decl
      if decl:is_axiom() then
         new_decl = mk_axiom(new_name, new_type)
      elseif decl:is_var_decl() then
         new_decl = mk_var_decl(new_name, new_type)
      else
         local new_value = process_expr(decl:type(), ps, ls)
         if decl:is_theorem() then
            new_decl = mk_theorem(new_name, new_type, new_value)
         else
            -- TODO(Leo): expose update_declaration functions in the
            -- Lua API.
            local attrs = {opaque=decl:opaque(),
                           weight=decl:weight(),
                           module_idx=decl:module_idx(),
                           use_conv_opt=decl:use_conv_opt()}
            new_decl = mk_definition(new_name, new_type, new_value, attrs)
         end
      end
      new_env = add_decl(new_env, new_decl)
      return new_name
   end

   -- Convert a constant from env into a constant for new_env
   function process_constant(e)
      if e:is_constant() then
         local n, ls = e:data()
         local new_e = map:find(e)
         if new_e then
            -- constant was already mapped to new_env
            return new_e
         else
            local decl  = env:find(n)
            if not decl then
               error("undefined constant '" .. n .. "'")
            end
            local new_name = process_declaration(decl, ls)
            local new_e    = mk_constant(new_name)
            map:insert(e, new_e)
            return new_e
         end
      end
   end

   -- Convert the expression e from env to new_env.
   -- The universe level parameters ps are instantiated with
   -- the explicit universe levels ls
   function process_expr(e, ps, ls)
      local new_e = e:instantiate_levels(ps, ls)
      -- replace all constants occurring in new_env with the
      -- corresponding ones from env
      return new_e:replace(process_constant)
   end

   -- Convert all constants occurring in t, and return the new environment.
   local new_t = process_expr(t, {}, {})
   return new_env, new_t
end

function display_env(env)
   env:for_each(function(d)
                   print(tostring(d:name()) .. " : " .. tostring(d:type()))
                end)
end

function example1()
   local env = environment()
   local l   = mk_param_univ("l")
   local v   = mk_param_univ("v")
   local A   = Local("A", mk_sort(l))
   local a   = Local("a", A)
   env = add_decl(env, mk_var_decl("eq", {l}, Pi(A, mk_arrow(A, A, Bool))))
   env = add_decl(env, mk_var_decl("group", {l}, mk_sort(l+1)))
   env = add_decl(env, mk_var_decl("prod", {l, v}, mk_arrow(mk_sort(l), mk_sort(v), mk_sort(max_univ(l, v)))))
   local eq2 = Const("eq", {2})
   local group1 = Const("group", {1})
   local group2 = Const("group", {2})
   local prod1  = Const("prod", {2, 3})(group1, group2)
   env:type_check(prod1) -- Type check prod1
   local prod2  = Const("prod", {3, 0})(prod1, eq2(Type, Bool, Bool))
   env:type_check(prod2) -- Type check prod1

   local new_env, new_prod2 = elim_univ_poly(env, prod2)
   print("converted term: " .. tostring(new_prod2))
   print("converted environment: ")
   display_env(new_env)
   new_env:type_check(new_prod2)
end

example1()
