-- Create a HoTT compatible environment.
-- That is,
--    Type.{0} is predicative
--    No proof irrelevance for Type.{0}
--    Proof irrelevance for Id types
local env = bare_environment({prop_proof_irrel=false, impredicative=false, cls_proof_irrel={"Id"}})
assert(not env:prop_proof_irrel())
assert(not env:impredicative())
assert(env:cls_proof_irrel():head() == name("Id"))
assert(env:cls_proof_irrel():tail():is_nil())
local l   = mk_param_univ("l")
local U_l = mk_sort(l)
local A   = Local("A", U_l)
env = add_decl(env, mk_var_decl("Id", {l}, Pi(A, mk_arrow(A, A, U_l))))
local Set = mk_sort(mk_level_zero())
env = add_decl(env, mk_var_decl("N", Set))
local N   = Const("N")
env = add_decl(env, mk_var_decl("a", N))
env = add_decl(env, mk_var_decl("b", N))
local a   = Const("a")
local b   = Const("b")
local Id_z = Const("Id", {mk_level_zero()})
env = add_decl(env, mk_axiom("H1", Id_z(N, a, b)))
env = add_decl(env, mk_axiom("H2", Id_z(N, a, b)))
local tc   = type_checker(env)
-- H1 and H2 are definitionally equal since both have type Id.{0} N a b
-- and Id is in env:cls_proof_irrel()
assert(tc:is_def_eq(Const("H1"), Const("H2")))
env = add_decl(env, mk_var_decl("Path", {l}, Pi(A, mk_arrow(A, A, U_l))))
local Path_z = Const("Path", {mk_level_zero()})
env = add_decl(env, mk_axiom("H3", Path_z(N, a, b)))
env = add_decl(env, mk_axiom("H4", Path_z(N, a, b)))
local tc   = type_checker(env)
assert(tc:is_def_eq(Const("H1"), Const("H2")))
assert(not tc:is_def_eq(Const("H3"), Const("H4")))
assert(tc:is_def_eq(tc:check(Const("H3")), tc:check(Const("H4"))))
print("H1 : " .. tostring(tc:check(Const("H1"))))
print("H2 : " .. tostring(tc:check(Const("H2"))))
print("H3 : " .. tostring(tc:check(Const("H3"))))
print("H4 : " .. tostring(tc:check(Const("H4"))))
print("N  : " .. tostring(get_formatter()(env, tc:check(Const("N")))))
-- N : Type.{0}
assert(not tc:is_def_eq(Const("a"), Const("b")))

