local env = environment()
local l      = mk_param_univ("l")
local A      = Local("A", mk_sort(l))
local a      = Local("a", A)
local b      = Local("b", A)
local P      = Local("P", mk_arrow(A, Prop))
env = add_decl(env, mk_definition("id", {l},
                                  Pi(A, mk_arrow(A, mk_arrow(A, Prop))),
                                  Fun(A, a, b, Pi(P, mk_arrow(P(a), P(b))))))
local id_l   = Const("id", {l})
local H      = Local("H", P(a))
env = add_decl(env, mk_theorem("refl", {l},
                               Pi(A, a, id_l(A, a, a)),
                               Fun(A, a, P, H, H)))
local H1     = Local("H1", id_l(A, a, b))
local H2     = Local("H2", P(a))
env = add_decl(env, mk_theorem("subst", {l},
                               Pi(A, P, a, b, H1, H2, P(b)),
                               Fun(A, P, a, b, H1, H2, H1(P, H2))))
local refl_l  = Const("refl", {l})
local subst_l = Const("subst", {l})
local x       = Local("x", A)
local H       = Local("H", id_l(A, a, b))
env = add_decl(env, mk_theorem("symm", {l},
                               Pi(A, a, b, H, id_l(A, b, a)),
                               Fun(A, a, b, H,
                                   subst_l(A, Fun(x, id_l(A, x, a)), a, b, H, refl_l(A, a)))))
local c      = Local("c", A)
local H1     = Local("H1", id_l(A, a, b))
local H2     = Local("H2", id_l(A, b, c))
env = add_decl(env, mk_theorem("trans", {l},
                               Pi(A, a, b, c, H1, H2, id_l(A, a, c)),
                               Fun(A, a, b, c, H1, H2,
                                   subst_l(A, Fun(x, id_l(A, a, x)), b, c, H2, H1))))
local symm_l = Const("symm", {l})
local trans_l = Const("trans", {l})
print(env:get("trans"):value())
env = env:add_universe("u")
local u       = mk_global_univ("u")
local tc      = type_checker(env)
print(tc:check(Const("trans", {u})))

local id_u    = Const("id", {u})
local refl_u  = Const("refl", {u})
local subst_u = Const("subst", {u})
local symm_u  = Const("symm", {u})
local trans_u = Const("trans", {u})
local A       = Local("A", mk_sort(u))
local d       = Local("d", A)
local H1      = Local("H1", id_u(A, b, a))
local H2      = Local("H2", id_u(A, b, c))
local H3      = Local("H3", id_u(A, c, d))
print(tc:check(Fun(A, a, b, c, d, H1, H2, H3,
                   trans_u(A, a, b, d,
                           symm_u(A, b, a, H1),
                           trans_u(A, b, c, d, H2, H3)))))
local g   = name_generator("tst")
local tc2 = type_checker(env, g)
print("=================")
local A     = Local("A", mk_sort(u))
local mf_ty = mk_metavar("f_ty", Pi(A, mk_sort(mk_meta_univ("l_f"))))
local f     = Local("f", mf_ty(A))
local a     = Local("a", A)
local mA1   = mk_metavar("A1",   Pi(A, f, a, mk_sort(mk_meta_univ("l_A1"))))
print(tc2:check(Fun(A, f, a,
                    id_u(mA1(A, f, a), f(a), a))))


