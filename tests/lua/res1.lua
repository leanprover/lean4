-- Create names for commonly used constants
local Or    = Const("or")
local Not   = Const("not")
local False = Const("false")

function init_env(env)
   -- Populate environment when declarations used by resolve_macro.
   -- This is a 'fake' environment used only for testing.
   local a   = Local("a", Prop)
   local b   = Local("b", Prop)
   local c   = Local("c", Prop)
   local Ha  = Local("Ha", a)
   local Hb  = Local("Hb", b)
   env = add_decl(env, mk_constant_assumption("or",  mk_arrow(Prop, Prop, Prop)))
   env = add_decl(env, mk_constant_assumption("not", mk_arrow(Prop, Prop)))
   env = add_decl(env, mk_constant_assumption("false", Prop))
   env = add_decl(env, mk_axiom({"or", "elim"}, Pi(a, b, c, mk_arrow(Or(a, b), mk_arrow(a, c), mk_arrow(b, c), c))))
   env = add_decl(env, mk_axiom({"or", "intro_left"}, Pi(a, Ha, b, Or(a, b))))
   env = add_decl(env, mk_axiom({"or", "intro_right"}, Pi(b, a, Hb, Or(a, b))))
   env = add_decl(env, mk_axiom("absurd_elim", Pi(a, b, mk_arrow(a, Not(a), b))))
   return env
end

function decl_bools(env, ls)
   for i = 1, #ls do
      env = add_decl(env, mk_constant_assumption(ls[i]:data(), Prop))
   end
   return env
end

function Consts(s)
   -- Auxiliary function for creating multiple constants
   local r = {}
   local i = 1
   for c in string.gmatch(s, '[^ ,;\t\n]+') do
      r[i] = Const(c)
      i = i + 1
   end
   return unpack(r)
end

function OR(...)
   -- Nary Or
   local arg = {...}
   if     #arg == 0 then
      return False
   elseif #arg == 1 then
      return arg[1]
   else
      local r = arg[#arg]
      for i = #arg-1, 1, -1 do
         r = Or(arg[i], r)
      end
      return r
   end
end

function print_types(env, ...)
   local arg = {...}
   local tc  = type_checker(env)
   for i = 1, #arg do
      print(tostring(arg[i]) .. " : " .. tostring(tc:check(arg[i])))
   end
end

function assert_some_axioms(env)
   -- Assert some clauses
   local l1, l2, l3, l4, l5, l6 = Consts("l1 l2 l3 l4 l5 l6")
   env = decl_bools(env, {l1, l2, l3, l4, l5})
   env = add_decl(env, mk_definition("l6", Prop, l3, {opaque=false})) -- l6 is alias for l3
   env = add_decl(env, mk_axiom("H1", OR(l1, l2, Not(l3))))
   env = add_decl(env, mk_axiom("H2", OR(l2, l3, l4)))
   env = add_decl(env, mk_axiom("H3", OR(Not(l1), l2, l4, l5)))
   env = add_decl(env, mk_axiom("H4", OR(l4, l6, Not(l5))))
   env = add_decl(env, mk_axiom("H5", OR(Not(l4), l3)))
   env = add_decl(env, mk_axiom("H6", Not(l3)))
   env = add_decl(env, mk_axiom("H7", Not(l2)))
   return env
end

local env = bare_environment({trust_lvl=1})
env = init_env(env)
env = assert_some_axioms(env)

local l1, l2, l3, l4, l5, l6 = Consts("l1 l2 l3 l4 l5 l6")
local H1, H2, H3, H4, H5, H6, H7 = Consts("H1 H2 H3 H4 H5 H6 H7")

local tc  = type_checker(env)
print(tc:check(Or))
print(tc:check(Const("absurd_elim")))
print(tc:check(H4))
local Pr1 = resolve_macro(l6, H2, H1)
local Pr2 = resolve_macro(l1, Pr1, H3)
assert(Pr1:is_macro())
assert(Pr1:macro_num_args() == 3)
assert(Pr1:macro_arg(0) == l6)
assert(Pr1:macro_def() == Pr2:macro_def())
assert(Pr1:data() == Pr1:macro_def())
assert(Pr1 == mk_macro(Pr1:macro_def(), {Pr1:macro_arg(0), Pr1:macro_arg(1), Pr1:macro_arg(2)}))
assert(Pr1:macro_def():name() == name("resolve"))
assert(Pr1:macro_def():trust_level() >= 0)
print(Pr1:macro_def():hash())
print(Pr1:macro_def())
print("-----------")
print(tc:check(H2))
print(tc:check(H1))
print(tc:check(Pr1))
print(tc:check(H3))
print(tc:check(Pr2))
local Pr3 = resolve_macro(l4, resolve_macro(l5, Pr2, H4), H5)
print(tc:check(Pr3))
local Pr4 = resolve_macro(l2, resolve_macro(l3, Pr3, H6), H7)
print("-----------")
print("proof for false: ")
print_types(env, H1, H2, H3, H4, H5, H6, H7)
print(tostring(Pr4) .. " : " .. tostring(tc:check(Pr4)))

print("----------------")
local env = bare_environment({trust_lvl=1})
env = init_env(env)
env = assert_some_axioms(env)
local tc  = type_checker(env)
-- Since the trust_lvl is 0, the macro will be expanded during type checking
print(tc:whnf(Pr1))
print(tc:check(Pr1))
print(tc:check(Pr4))

print(env:normalize(Pr4))

local a = Const("a")
assert(not pcall(function() a:macro_num_args() end))
assert(not pcall(function() a:let_name() end))
assert(not pcall(function() mk_arrow(a) end))
