local env = environment()
env = env:begin_section_scope()
local nat      = Const("nat")
env = add_inductive(env,
                    "nat", Type,
                    "zero", nat,
                    "succ", mk_arrow(nat, nat))
local zero     = Const("zero")
local succ     = Const("succ")

env = env:begin_section_scope()
env = env:add_global_level("l")
local l = mk_global_univ("l")
env = env:add(check(env, mk_var_decl("A", mk_sort(l))), binder_info(true))
env = env:add(check(env, mk_var_decl("B", mk_sort(l))), binder_info(true))
local A = Const("A")
local vector = Const("vector")
local n      = Local("n", nat)
env = add_inductive(env,
                    "vector", mk_arrow(nat, mk_sort(max_univ(l, 1))),
                    "nil", vector(zero),
                    "cons", Pi(n, mk_arrow(A, vector(n), vector(succ(n)))))

print(env:find("vector_rec"):type())
assert(env:find("cons"):type() == Pi(n, mk_arrow(A, vector(n), vector(succ(n)))))
env = env:end_scope()
print(env:find("vector_rec"):type())
print(env:find("cons"):type())
local l = mk_param_univ("l")
local A = Local("A", mk_sort(l))
local vector = Const("vector", {l})
assert(env:find("cons"):type() == Pi({A, n}, mk_arrow(A, vector(A, n), vector(A, succ(n)))))
env = env:end_scope()

print(env:find("vector_rec"):type())
print(env:find("cons"):type())
env:export("sect8_mod.olean")
local env2 = import_modules("sect8_mod")
assert(env:find("vector_rec"):type() == env2:find("vector_rec"):type())
