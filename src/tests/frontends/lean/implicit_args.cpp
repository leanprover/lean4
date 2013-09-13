/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/occurs.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "library/metavar.h"
#include "library/printer.h"
#include "library/basic_thms.h"
#include "library/all/all.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/elaborator_exception.h"
using namespace lean;

expr elaborate(expr const & e, frontend const & env) {
    elaborator elb(env);
    return elb(e);
}

// Check elaborator success
static void success(expr const & e, expr const & expected, frontend const & env) {
    std::cout << "\n" << e << "\n------>\n";
    try {
        std::cout << elaborate(e, env) << "\n";
    } catch (unification_app_mismatch_exception & ex) {
        std::cout << "Error at " << mk_pair(ex.get_expr(), ex.get_context()) << "\n";
    } catch (unification_type_mismatch_exception & ex) {
        std::cout << "Error at " << mk_pair(ex.get_expr(), ex.get_context()) << " " << ex.what() << "\n";
        std::cout << "Elaborator:\n"; ex.get_elaborator().display(std::cout); std::cout << "-----------------\n";
    }
    lean_assert(elaborate(e, env) == expected);
    try {
        std::cout << infer_type(elaborate(e, env), env) << "\n";
    } catch (app_type_mismatch_exception & ex) {
        context const & ctx = ex.get_context();
        std::cout << "Application type mismatch at\n"
                  << "  " << mk_pair(ex.get_application(), ctx) << "\n";
        lean_unreachable();
    }
}

// Check elaborator failure
static void fails(expr const & e, frontend const & env) {
    try {
        expr new_e = elaborate(e, env);
        std::cout << "new_e: " << new_e << std::endl;
        lean_unreachable();
    } catch (exception &) {
    }
}

// Check elaborator partial success (i.e., result still contain some metavariables */
static void unsolved(expr const & e, frontend const & env) {
    try {
        std::cout << "\n" << e << "\n------>\n" << elaborate(e, env) << "\n";
        lean_unreachable();
    } catch (unsolved_placeholder_exception) {
    }
}

#define _ mk_placholder()

static void tst1() {
    frontend env;
    expr A = Const("A");
    expr B = Const("B");
    expr F = Const("F");
    expr g = Const("g");
    expr a = Const("a");
    expr Nat  = Const("N");
    expr Real = Const("R");
    env.add_var("N", Type());
    env.add_var("R", Type());
    env.add_var("F", Pi({{A, Type()}, {B, Type()}, {g, A >> B}}, A));
    env.add_var("f", Nat >> Real);
    expr f = Const("f");
    success(F(_, _, f), F(Nat, Real, f), env);
    // fails(F(_, Bool, f), env);
    success(F(_, _, Fun({a, Nat}, a)), F(Nat, Nat, Fun({a, Nat}, a)), env);
}

static void tst2() {
    frontend env;
    expr a  = Const("a");
    expr b  = Const("b");
    expr c  = Const("c");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    env.add_var("a", Bool);
    env.add_var("b", Bool);
    env.add_var("c", Bool);
    env.add_axiom("H1", Eq(a, b));
    env.add_axiom("H2", Eq(b, c));
    success(Trans(_, _, _, _, H1, H2), Trans(Bool, a, b, c, H1, H2), env);
    success(Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1)),
            Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1)), env);
    success(Symm(_, _, _, Trans(_, _ , _ , _ , Symm(_, _, _, H2), Symm(_, _, _, H1))),
            Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), env);
    env.add_axiom("H3", a);
    expr H3 = Const("H3");
    success(EqTIntro(_, EqMP(_, _, Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1))), H3)),
            EqTIntro(c, EqMP(a, c, Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), H3)),
            env);
}

static void tst3() {
    frontend env;
    expr Nat = Const("N");
    env.add_var("N", Type());
    env.add_var("vec", Nat >> Type());
    expr n   = Const("n");
    expr vec = Const("vec");
    env.add_var("f", Pi({n, Nat}, vec(n) >> Nat));
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr H = Const("H");
    expr fact = Const("fact");
    env.add_var("a", Nat);
    env.add_var("b", Nat);
    env.add_definition("fact", Bool, Eq(a, b));
    env.add_axiom("H", fact);
    success(Congr2(_, _, _, _, f, H),
            Congr2(Nat, Fun({n, Nat}, vec(n) >> Nat), a, b, f, H), env);
    env.add_var("g", Pi({n, Nat}, vec(n) >> Nat));
    expr g = Const("g");
    env.add_axiom("H2", Eq(f, g));
    expr H2 = Const("H2");
    success(Congr(_, _, _, _, _, _, H2, H),
            Congr(Nat, Fun({n, Nat}, vec(n) >> Nat), f, g, a, b, H2, H), env);
    success(Congr(_, _, _, _, _, _, Refl(_, f), H),
            Congr(Nat, Fun({n, Nat}, vec(n) >> Nat), f, f, a, b, Refl(Pi({n, Nat}, vec(n) >> Nat), f), H), env);
    success(Refl(_, a), Refl(Nat, a), env);
}

static void tst4() {
    frontend env;
    expr Nat = Const("N");
    env.add_var("N", Type());
    expr R   = Const("R");
    env.add_var("R", Type());
    env.add_var("a", Nat);
    expr a   = Const("a");
    expr f   = Const("f");
    env.add_var("f", Nat >> ((R >> Nat) >> R));
    expr x   = Const("x");
    expr y   = Const("y");
    expr z   = Const("z");
    success(Fun({{x, _}, {y, _}}, f(x, y)),
            Fun({{x, Nat}, {y, R >> Nat}}, f(x, y)), env);
    success(Fun({{x, _}, {y, _}, {z, _}}, Eq(f(x, y), f(x, z))),
            Fun({{x, Nat}, {y, R >> Nat}, {z, R >> Nat}}, Eq(f(x, y), f(x, z))), env);
    expr A   = Const("A");
    success(Fun({{A, Type()}, {x, _}, {y, _}, {z, _}}, Eq(f(x, y), f(x, z))),
            Fun({{A, Type()}, {x, Nat}, {y, R >> Nat}, {z, R >> Nat}}, Eq(f(x, y), f(x, z))), env);
}

static void tst5() {
    frontend env;
    expr A = Const("A");
    expr B = Const("B");
    expr a = Const("a");
    expr b = Const("b");
    expr f = Const("f");
    expr g = Const("g");
    expr Nat = Const("N");
    env.add_var("N", Type());
    env.add_var("f", Pi({{A, Type()}, {a, A}, {b, A}}, A));
    env.add_var("g", Nat >> Nat);
    success(Fun({{a, _}, {b, _}}, g(f(_, a, b))),
            Fun({{a, Nat}, {b, Nat}}, g(f(Nat, a, b))), env);
}

static void tst6() {
    frontend env;
    expr lst  = Const("list");
    expr nil  = Const("nil");
    expr cons = Const("cons");
    expr N    = Const("N");
    expr A    = Const("A");
    expr f    = Const("f");
    expr l    = Const("l");
    expr a    = Const("a");
    env.add_var("N", Type());
    env.add_var("list", Type() >> Type());
    env.add_var("nil", Pi({A, Type()}, lst(A)));
    env.add_var("cons", Pi({{A, Type()}, {a, A}, {l, lst(A)}}, lst(A)));
    env.add_var("f", lst(N >> N) >> Bool);
    success(Fun({a, _}, f(cons(_, a, cons(_, a, nil(_))))),
            Fun({a, N >> N}, f(cons(N >> N, a, cons(N >> N, a, nil(N >> N))))), env);
}

static void tst7() {
    frontend env;
    expr x = Const("x");
    expr omega = mk_app(Fun({x, _}, x(x)), Fun({x, _}, x(x)));
    fails(omega, env);
}

static void tst8() {
    frontend env;
    expr B = Const("B");
    expr A = Const("A");
    expr x = Const("x");
    expr f = Const("f");
    env.add_var("f", Pi({B, Type()}, B >> B));
    success(Fun({{A, Type()}, {B, Type()}, {x, _}}, f(B, x)),
            Fun({{A, Type()}, {B, Type()}, {x, B}}, f(B, x)), env);
    fails(Fun({{x, _}, {A, Type()}}, f(A, x)), env);
    success(Fun({{A, Type()}, {x, _}}, f(A, x)),
            Fun({{A, Type()}, {x, A}}, f(A, x)), env);
    success(Fun({{A, Type()}, {B, Type()}, {x, _}}, f(A, x)),
            Fun({{A, Type()}, {B, Type()}, {x, A}}, f(A, x)), env);
    success(Fun({{A, Type()}, {B, Type()}, {x, _}}, Eq(f(B, x), f(_, x))),
            Fun({{A, Type()}, {B, Type()}, {x, B}}, Eq(f(B, x), f(B, x))), env);
    success(Fun({{A, Type()}, {B, _}, {x, _}}, Eq(f(B, x), f(_, x))),
            Fun({{A, Type()}, {B, Type()}, {x, B}}, Eq(f(B, x), f(B, x))), env);
    unsolved(Fun({{A, _}, {B, _}, {x, _}}, Eq(f(B, x), f(_, x))), env);
}

static void tst9() {
    frontend env;
    expr A = Const("A");
    expr B = Const("B");
    expr f = Const("f");
    expr g = Const("g");
    expr x = Const("x");
    expr y = Const("y");
    env.add_var("N", Type());
    env.add_var("f", Pi({A, Type()}, A >> A));
    expr N = Const("N");
    success(Fun({g, Pi({A, Type()}, A >> (A >> Bool))}, g(_, True, False)),
            Fun({g, Pi({A, Type()}, A >> (A >> Bool))}, g(Bool, True, False)),
            env);
    success(Fun({g, Pi({A, TypeU}, A >> (A >> Bool))}, g(_, Bool, Bool)),
            Fun({g, Pi({A, TypeU}, A >> (A >> Bool))}, g(Type(), Bool, Bool)),
            env);
    success(Fun({g, Pi({A, TypeU}, A >> (A >> Bool))}, g(_, Bool, N)),
            Fun({g, Pi({A, TypeU}, A >> (A >> Bool))}, g(Type(), Bool, N)),
            env);
    success(Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g(_,
                  Fun({{x, _}, {y, _}}, Eq(f(_, x), f(_, y))),
                  Fun({{x, N}, {y, Bool}}, True))),
            Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g((N >> (Bool >> Bool)),
                  Fun({{x, N}, {y, Bool}}, Eq(f(N, x), f(Bool, y))),
                  Fun({{x, N}, {y, Bool}}, True))), env);

    success(Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g(_,
                  Fun({{x, N}, {y, _}}, Eq(f(_, x), f(_, y))),
                  Fun({{x, _}, {y, Bool}}, True))),
            Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g((N >> (Bool >> Bool)),
                  Fun({{x, N}, {y, Bool}}, Eq(f(N, x), f(Bool, y))),
                  Fun({{x, N}, {y, Bool}}, True))), env);
}

static void tst10() {
    frontend env;
    expr A = Const("A");
    expr B = Const("B");
    expr C = Const("C");
    expr a = Const("a");
    expr b = Const("b");
    expr eq = Const("eq");
    env.add_var("eq", Pi({A, Type()}, A >> (A >> Bool)));
    success(Fun({{A, Type()}, {B, Type()}, {a, _}, {b, B}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, B}, {b, B}}, eq(B, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, _}, {b, A}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, A}, {b, A}}, eq(A, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, A}, {b, _}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, A}, {b, A}}, eq(A, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, B}, {b, _}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, B}, {b, B}}, eq(B, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, B}, {b, _}, {C, Type()}}, eq(_, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, B}, {b, B}, {C, Type()}}, eq(B, a, b)), env);
    fails(Fun({{A, Type()}, {B, Type()}, {a, _}, {b, _}, {C, Type()}}, eq(C, a, b)), env);
    success(Fun({{A, Type()}, {B, Type()}, {a, _}, {b, _}, {C, Type()}}, eq(B, a, b)),
            Fun({{A, Type()}, {B, Type()}, {a, B}, {b, B}, {C, Type()}}, eq(B, a, b)), env);
}


static void tst11() {
    frontend env;
    expr a  = Const("a");
    expr b  = Const("b");
    expr c  = Const("c");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    env.add_var("a", Bool);
    env.add_var("b", Bool);
    env.add_var("c", Bool);
    success(Fun({{H1, Eq(a, b)}, {H2, Eq(b, c)}},
                Trans(_, _, _, _, H1, H2)),
            Fun({{H1, Eq(a, b)}, {H2, Eq(b, c)}},
                Trans(Bool, a, b, c, H1, H2)),
            env);
    expr H3 = Const("H3");
    success(Fun({{H1, Eq(a, b)}, {H2, Eq(b, c)}, {H3, a}},
                EqTIntro(_, EqMP(_, _, Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1))), H3))),
            Fun({{H1, Eq(a, b)}, {H2, Eq(b, c)}, {H3, a}},
                EqTIntro(c, EqMP(a, c, Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), H3))),
            env);
    frontend env2;
    success(Fun({{a, Bool}, {b, Bool}, {c, Bool}, {H1, Eq(a, b)}, {H2, Eq(b, c)}, {H3, a}},
                EqTIntro(_, EqMP(_, _, Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1))), H3))),
            Fun({{a, Bool}, {b, Bool}, {c, Bool}, {H1, Eq(a, b)}, {H2, Eq(b, c)}, {H3, a}},
                EqTIntro(c, EqMP(a, c, Symm(Bool, c, a, Trans(Bool, c, b, a, Symm(Bool, b, c, H2), Symm(Bool, a, b, H1))), H3))),
            env2);
    expr A = Const("A");
    success(Fun({{A, Type()}, {a, A}, {b, A}, {c, A}, {H1, Eq(a, b)}, {H2, Eq(b, c)}},
                Symm(_, _, _, Trans(_, _, _, _, Symm(_, _, _, H2), Symm(_, _, _, H1)))),
            Fun({{A, Type()}, {a, A}, {b, A}, {c, A}, {H1, Eq(a, b)}, {H2, Eq(b, c)}},
                Symm(A, c, a, Trans(A, c, b, a, Symm(A, b, c, H2), Symm(A, a, b, H1)))),
            env2);
}

void tst12() {
    frontend env;
    expr A  = Const("A");
    expr B  = Const("B");
    expr a  = Const("a");
    expr b  = Const("b");
    expr eq = Const("eq");
    env.add_var("eq", Pi({A, Type(level()+1)}, A >> (A >> Bool)));
    success(eq(_, Fun({{A, Type()}, {a, _}}, a), Fun({{B, Type()}, {b, B}}, b)),
            eq(Pi({A, Type()}, A >> A), Fun({{A, Type()}, {a, A}}, a), Fun({{B, Type()}, {b, B}}, b)),
            env);
}

void tst13() {
    frontend env;
    expr A  = Const("A");
    expr h  = Const("h");
    expr f  = Const("f");
    expr a  = Const("a");
    env.add_var("h", Pi({A, Type()}, A) >> Bool);
    success(Fun({{f, Pi({A, Type()}, _)}, {a, Bool}}, h(f)),
            Fun({{f, Pi({A, Type()}, A)}, {a, Bool}}, h(f)),
            env);
}

void tst14() {
    frontend env;
    expr R  = Const("R");
    expr A  = Const("A");
    expr r  = Const("r");
    expr eq = Const("eq");
    expr f  = Const("f");
    expr g  = Const("g");
    expr h  = Const("h");
    expr D  = Const("D");
    env.add_var("R", Type() >> Bool);
    env.add_var("r", Pi({A, Type()}, R(A)));
    env.add_var("h", Pi({A, Type()}, R(A)) >> Bool);
    env.add_var("eq", Pi({A, Type(level()+1)}, A >> (A >> Bool)));
    success(Let({{f, Fun({A, Type()}, r(_))},
                 {g, Fun({A, Type()}, r(_))},
                 {D, Fun({A, Type()}, eq(_, f(A), g(_)))}},
                h(f)),
            Let({{f, Fun({A, Type()}, r(A))},
                 {g, Fun({A, Type()}, r(A))},
                 {D, Fun({A, Type()}, eq(R(A), f(A), g(A)))}},
                h(f)),
            env);
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    tst11();
    tst12();
    tst13();
    tst14();
    return has_violations() ? 1 : 0;
}
