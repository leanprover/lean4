local env = bare_environment()
local l      = mk_param_univ("l")
local A      = Const("A")
local a      = Const("a")
local b      = Const("b")
local P      = Const("P")
env = add_decl(env, mk_definition("id", {l},
                                  Pi(A, mk_sort(l), mk_arrow(A, mk_arrow(A, Bool))),
                                  Fun({{A, mk_sort(l)}, {a, A}, {b, A}}, Pi(P, mk_arrow(A, Bool), mk_arrow(P(a), P(b))))))
local id_l   = Const("id", {l})
local H      = Const("H")
env = add_decl(env, mk_theorem("refl", {l},
                               Pi({{A, mk_sort(l)}, {a, A}}, id_l(A, a, a)),
                               Fun({{A, mk_sort(l)}, {a, A}, {P, mk_arrow(A, Bool)}, {H, P(a)}}, H)))
local H1     = Const("H1")
local H2     = Const("H2")
env = add_decl(env, mk_theorem("subst", {l},
                               Pi({{A, mk_sort(l)}, {P, mk_arrow(A, Bool)}, {a, A}, {b, A}, {H1, id_l(A, a, b)}, {H2, P(a)}}, P(b)),
                               Fun({{A, mk_sort(l)}, {P, mk_arrow(A, Bool)}, {a, A}, {b, A}, {H1, id_l(A, a, b)}, {H2, P(a)}},
                                   H1(P, H2))))
local refl_l  = Const("refl", {l})
local subst_l = Const("subst", {l})
local x       = Const("x")
env = add_decl(env, mk_theorem("symm", {l},
                               Pi({{A, mk_sort(l)}, {a, A}, {b, A}, {H, id_l(A, a, b)}}, id_l(A, b, a)),
                               Fun({{A, mk_sort(l)}, {a, A}, {b, A}, {H, id_l(A, a, b)}},
                                   subst_l(A, Fun(x, A, id_l(A, x, a)), a, b, H, refl_l(A, a)))))
local c       = Const("c")
env = add_decl(env, mk_theorem("trans", {l},
                               Pi({{A, mk_sort(l)}, {a, A}, {b, A}, {c, A}, {H1, id_l(A, a, b)}, {H2, id_l(A, b, c)}}, id_l(A, a, c)),
                               Fun({{A, mk_sort(l)}, {a, A}, {b, A}, {c, A}, {H1, id_l(A, a, b)}, {H2, id_l(A, b, c)}},
                                   subst_l(A, Fun(x, A, id_l(A, a, x)), b, c, H2, H1))))
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
local d       = Const("d")
local H3      = Const("H3")
print(tc:check(Fun({{A, mk_sort(u)}, {a, A}, {b, A}, {c, A}, {d, A},
                    {H1, id_u(A, b, a)},
                    {H2, id_u(A, b, c)},
                    {H3, id_u(A, c, d)}},
                   trans_u(A, a, b, d,
                           symm_u(A, b, a, H1),
                           trans_u(A, b, c, d, H2, H3)))))
local cs  = {}
local g   = name_generator("tst")
local tc2 = type_checker(env, g, constraint_handler(function (c) print(c); cs[#cs+1] = c end))
print("=================")
local f     = Const("f")
local mf_ty = mk_metavar("f_ty", Pi(A, mk_sort(u), mk_sort(mk_meta_univ("l_f"))))
local mA1   = mk_metavar("A1",   Pi({{A, mk_sort(u)}, {f, mf_ty(A)}, {a, A}}, mk_sort(mk_meta_univ("l_A1"))))
print(tc2:check(Fun({{A, mk_sort(u)}, {f, mf_ty(A)}, {a, A}},
                    id_u(mA1(A, f, a), f(a), a))))


local cs  = {}
local tc2 = type_checker(env, g, constraint_handler(function (c) print(c); cs[#cs+1] = c end))
local scope = {{A, mk_sort(u)}, {a, A}, {b, A}, {c, A}, {d, A}, {H1, id_u(A, b, a)},
               {H2, id_u(A, b, c)}, {H3, id_u(A, c, d)}}
local mP  = mk_metavar("P", Pi(scope, mk_metavar("P_ty", Pi(scope, mk_sort(mk_meta_univ("l_P"))))(A, a, b, c, d, H1, H2, H3)))(A, a, b, c, d, H1, H2, H3)
local ma  = mk_metavar("a", Pi(scope, mk_metavar("a_ty", Pi(scope, mk_sort(mk_meta_univ("l_a"))))(A, a, b, c, d, H1, H2, H3)))(A, a, b, c, d, H1, H2, H3)
local mb  = mk_metavar("b", Pi(scope, mk_metavar("b_ty", Pi(scope, mk_sort(mk_meta_univ("l_b"))))(A, a, b, c, d, H1, H2, H3)))(A, a, b, c, d, H1, H2, H3)
local mA1  = mk_metavar("A1", Pi(scope, mk_sort(mk_meta_univ("l_A1"))))(A, a, b, c, d, H1, H2, H3)
local mA2  = mk_metavar("A2", Pi(scope, mk_sort(mk_meta_univ("l_A2"))))(A, a, b, c, d, H1, H2, H3)
print("================")
print(tc2:check(Fun(scope,
                     subst_u(mA1, mP, mb, ma,
                             H1,
                             trans_u(mA2, b, c, d, H2, H3)))))
