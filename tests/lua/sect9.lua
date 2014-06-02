local env = environment()
env = env:begin_section_scope()
env = env:begin_section_scope()
local nat      = Const("nat")
env = add_inductive(env,
                    "nat", Type,
                    "zero", nat,
                    "succ", mk_arrow(nat, nat))
local zero     = Const("zero")
local succ     = Const("succ")
local one      = succ(zero)
env = env:add_global_level("l")
local l = mk_global_univ("l")
env = env:add(check(env, mk_var_decl("A", mk_sort(l))), binder_info(true))
env = env:add(check(env, mk_var_decl("B", mk_sort(l))), binder_info(true))
local A = Const("A")
local l1 = mk_param_univ("l1")
local D = Const("D", {l1})
local n = Local("n", nat)
env = add_inductive(env,
                    "D", {l1}, 1, mk_arrow(nat, nat, mk_sort(max_univ(l1, l, 1))),
                    "mk1", Pi(n, mk_arrow(A, D(n, one))),
                    "mk0", Pi(n, mk_arrow(A, A, D(n, zero))))
print(env:find("D_rec"):type())
env = env:end_scope()
env = env:end_scope()
print(env:find("D_rec"):type())

local l = mk_param_univ("l")
local A = Local("A", mk_sort(l))
local D = Const("D", {l, l1})
print(env:find("mk1"):type())
assert(env:find("mk1"):type() == Pi({A, n}, mk_arrow(A, D(A, n, one))))
