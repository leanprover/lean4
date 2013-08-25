/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "test.h"
#include "metavar_env.h"
#include "elaborator.h"
#include "printer.h"
#include "occurs.h"
#include "abstract.h"
#include "toplevel.h"
#include "basic_thms.h"
#include "type_check.h"
#include "kernel_exception.h"
using namespace lean;

static name g_placeholder_name("_");
/** \brief Return a new placeholder expression. To be able to track location,
    a new constant for each placeholder.
*/
expr mk_placholder() {
    return mk_constant(g_placeholder_name);
}

/** \brief Return true iff the given expression is a placeholder. */
bool is_placeholder(expr const & e) {
    return is_constant(e) && const_name(e) == g_placeholder_name;
}

/** \brief Return true iff the given expression contains placeholders. */
bool has_placeholder(expr const & e) {
    return occurs(mk_placholder(), e);
}

std::ostream & operator<<(std::ostream & out, metavar_env const & uf) { uf.display(out); return out; }

/**
   \brief Auxiliary function for #replace_placeholders_with_metavars
*/
static expr replace(expr const & e, context const & ctx, metavar_env & menv) {
    switch (e.kind()) {
    case expr_kind::Constant:
        if (is_placeholder(e)) {
            return menv.mk_metavar(ctx);
        } else {
            return e;
        }
    case expr_kind::Var: case expr_kind::Type: case expr_kind::Value:
        return e;
    case expr_kind::App:
        return update_app(e, [&](expr const & c) { return replace(c, ctx, menv); });
    case expr_kind::Eq:
        return update_eq(e, [&](expr const & l, expr const & r) { return mk_pair(replace(l, ctx, menv), replace(r, ctx, menv)); });
    case expr_kind::Lambda:
    case expr_kind::Pi:
        return update_abst(e, [&](expr const & d, expr const & b) {
                expr new_d = replace(d, ctx, menv);
                expr new_b = replace(b, extend(ctx, abst_name(e), new_d), menv);
                return mk_pair(new_d, new_b);
            });
    case expr_kind::Let:
        return update_let(e, [&](expr const & v, expr const & b) {
                expr new_v = replace(v, ctx, menv);
                expr new_b = replace(b, extend(ctx, abst_name(e), expr(), new_v), menv);
                return mk_pair(new_v, new_b);
            });
    }
    lean_unreachable();
    return e;
}

/**
   \brief Replace placeholders with fresh meta-variables.
*/
expr replace_placeholders_with_metavars(expr const & e, metavar_env & menv) {
    return replace(e, context(), menv);
}

expr elaborate(expr const & e, environment const & env) {
    elaborator elb(env);
    expr new_e = replace_placeholders_with_metavars(e, elb.menv());
    return elb(new_e);
}

static void tst1() {
    expr m1 = mk_metavar(0);
    expr m2 = mk_metavar(1);
    expr a  = Const("a");
    expr f  = Const("f");
    lean_assert(is_metavar(m1));
    lean_assert(!is_metavar(a));
    lean_assert(metavar_idx(m1) == 0);
    lean_assert(metavar_idx(m2) == 1);
    lean_assert(m1 != m2);
    lean_assert(a != m1);
    std::cout << m1 << " " << m2 << "\n";
    lean_assert(has_metavar(m1));
    lean_assert(has_metavar(f(f(f(m1)))));
    lean_assert(!has_metavar(f(f(a))));
}

static void tst2() {
    environment env;
    metavar_env u(env);
    expr m1 = u.mk_metavar();
    expr m2 = u.mk_metavar();
    expr m3 = u.mk_metavar();
    lean_assert(!u.is_assigned(m1));
    lean_assert(!u.is_assigned(m2));
    lean_assert(!u.is_assigned(m3));
    expr f = Const("f");
    expr t1 = f(m1, m2);
    expr t2 = f(m1, m1);
    lean_assert(t1 != t2);
    // m1 <- m2
    u.assign(m1, m2);
    std::cout << u << "\n";
    lean_assert(u.root_at(m2, 0) == m2);
    lean_assert(u.root_at(m1, 0) == m2);
    expr a = Const("a");
    expr b = Const("b");
    expr g = Const("g");
    expr t3 = f(a, m1);
    expr t4 = f(m2, a);
    expr t5 = f(a, a);
    lean_assert(t3 != t4);
    lean_assert(t4 != t5);
    u.assign(m2, a);
    u.assign(m3, b);
    std::cout << u << "\n";
    expr m4 = u.mk_metavar();
    std::cout << u << "\n";
    u.assign(m4, m1);
    std::cout << u << "\n";
    expr m5 = u.mk_metavar();
    expr m6 = u.mk_metavar();
    u.assign(m5, m6);
    metavar_env u2(u);
    u.assign(m5, m3);
    std::cout << u << "\n";
    u2.assign(m5, m2);
    std::cout << u2 << "\n";
}

static void tst3() {
    environment env;
    metavar_env uenv(env);
    expr m1 = uenv.mk_metavar();
    expr f  = Const("f");
    expr a  = Const("a");
    expr b  = Const("b");
    expr g  = Const("g");
    expr m2 = uenv.mk_metavar();
    uenv.assign(m2, f(m1, a));
    uenv.assign(m1, b);
    std::cout << uenv.instantiate_metavars(g(m2,b)) << "\n";
    lean_assert(uenv.instantiate_metavars(g(m2,b)) == g(f(b,a), b));
    lean_assert(uenv.instantiate_metavars(g(m2,f(a,m1))) == g(f(b,a),f(a,b)));
    expr m3 = uenv.mk_metavar();
    expr m4 = uenv.mk_metavar();
    uenv.assign(m3, f(m4));
    try {
        uenv.assign(m4, f(m3));
        lean_unreachable();
    } catch (exception) {
    }
}

static void tst4() {
    environment env;
    metavar_env uenv(env);
    expr m1 = uenv.mk_metavar();
    expr m2 = uenv.mk_metavar();
    uenv.assign(m1, m2);
    expr f  = Const("f");
    expr a  = Const("a");
    expr t  = uenv.instantiate_metavars(f(m1,f(a, m1)));
    std::cout << t << "\n";
    lean_assert(t == f(m2, f(a, m2)));
}

static void tst5() {
    environment env;
    env.add_var("A", Type());
    env.add_var("B", Type());
    expr A  = Const("A");
    expr B  = Const("B");
    env.add_definition("F", Type(), A >> B);
    env.add_definition("G", Type(), B >> B);
    metavar_env uenv(env);
    expr m1 = uenv.mk_metavar();
    expr m2 = uenv.mk_metavar();
    expr m3 = uenv.mk_metavar();
    expr m4 = uenv.mk_metavar();
    expr F  = Const("F");
    expr G  = Const("G");
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    expr b  = Const("b");
    expr x  = Const("x");
    expr Id = Fun({x, A}, x);
    expr t1 = f(m1, g(a, F));
    expr t2 = f(g(a, b), Id(g(m2, m3 >> m4)));
    metavar_env uenv2(uenv);
    uenv2.unify(t1, t2);
    std::cout << uenv2 << "\n";
    lean_assert(uenv2.root_at(m1,0) == g(a, b));
    lean_assert(uenv2.root_at(m2,0) == a);
    lean_assert(uenv2.root_at(m3,0) == A);
    lean_assert(uenv2.root_at(m4,0) == B);
    lean_assert(uenv2.instantiate_metavars(t1) == f(g(a, b), g(a, F)));
    lean_assert(uenv2.instantiate_metavars(t2) == f(g(a, b), Id(g(a, A >> B))));
    metavar_env uenv3(uenv);
    expr t3 = f(m1, m1 >> m1);
    expr t4 = f(m2 >> m2, m3);
    uenv3.unify(t3, t4);
    std::cout << uenv3 << "\n";
    uenv3.unify(m1, G);
    std::cout << uenv3 << "\n";
    std::cout << uenv3.instantiate_metavars(t3) << "\n";
}

static void tst6() {
    environment env;
    env.add_var("A", Type());
    expr A = Const("A");
    expr f = Const("f");
    expr g = Const("g");
    expr a = Const("a");
    expr b = Const("b");
    context ctx1;
    ctx1 = extend(extend(ctx1, "x", A >> A), "y", A);
    metavar_env uenv(env);
    expr m1 = uenv.mk_metavar();
    expr m2 = uenv.mk_metavar(ctx1);
    context ctx2;
    ctx2 = extend(ctx2, "x", m1);
    expr m3 = uenv.mk_metavar(ctx2);
    metavar_env uenv2(uenv);
    expr t1 = f(m2,    m3);
    expr t2 = f(g(m3), Var(0));
    std::cout << "----------------\n";
    std::cout << uenv << "\n";
    uenv.unify(t1, t2, ctx2);
    std::cout << uenv << "\n";
    std::cout << uenv.instantiate_metavars(t1) << "\n";
    std::cout << uenv.instantiate_metavars(t2) << "\n";
    lean_assert(uenv.instantiate_metavars(t1) == uenv.instantiate_metavars(t2));
    lean_assert(uenv.instantiate_metavars(t2) == f(g(Var(0)), Var(0)));
    lean_assert(uenv.instantiate_metavars(m1) == A >> A);
    expr t3 = f(m2);
    expr t4 = f(m3);
    uenv2.unify(t3, t4);
    std::cout << "----------------\n";
    std::cout << uenv2 << "\n";
    lean_assert(uenv2.instantiate_metavars(m1) == A >> A);
    lean_assert(length(uenv2.get_context(m2)) == length(uenv2.get_context(m3)));
}

static void tst7() {
    environment env;
    env.add_var("A", Type());
    env.add_var("B", Type());
    expr A  = Const("A");
    expr B  = Const("B");
    env.add_definition("F", Type(), A >> B);
    env.add_definition("G", Type(), B >> B);
    name_set S;
    S.insert("G");
    metavar_env uenv(env, &S);
    expr m1 = uenv.mk_metavar();
    expr m2 = uenv.mk_metavar();
    expr m3 = uenv.mk_metavar();
    expr m4 = uenv.mk_metavar();
    expr F  = Const("F");
    expr G  = Const("G");
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    expr b  = Const("b");
    expr x  = Const("x");
    expr Id = Fun({x, A}, x);
    expr t1 = f(m1, g(a, F));
    expr t2 = f(g(a, b), Id(g(m2, m3 >> m4)));
    metavar_env uenv2(uenv);
    try {
        uenv2.unify(t1, t2);
        lean_unreachable();
    } catch (exception) {
        // It failed because "F" is not in the set of
        // available definitions.
    }
    S.insert("F");
    uenv.unify(t1, t2);
    std::cout << uenv.instantiate_metavars(t1) << "\n";
    std::cout << uenv.instantiate_metavars(t2) << "\n";
}

// Check elaborator success
static void success(expr const & e, expr const & expected, environment const & env) {
    std::cout << "\n" << e << "\n------>\n" << elaborate(e, env) << "\n";
    lean_assert(elaborate(e, env) == expected);
    std::cout << infer_type(elaborate(e, env), env) << "\n";
}

// Check elaborator failure
static void fails(expr const & e, environment const & env) {
    try {
        elaborate(e, env);
        lean_unreachable();
    } catch (exception &) {
    }
}

// Check elaborator partial success (i.e., result still contain some metavariables */
static void unsolved(expr const & e, environment const & env) {
    std::cout << "\n" << e << "\n------>\n" << elaborate(e, env) << "\n";
    lean_assert(has_metavar(elaborate(e, env)));
}

static void tst8() {
    environment env;
    expr A = Const("A");
    expr B = Const("B");
    expr F = Const("F");
    expr g = Const("g");
    expr a = Const("a");
    expr Nat  = Const("Nat");
    expr Real = Const("Real");
    env.add_var("Nat", Type());
    env.add_var("Real", Type());
    env.add_var("F", Pi({{A, Type()}, {B, Type()}, {g, A >> B}}, A));
    env.add_var("f", Nat >> Real);
    expr _ = mk_placholder();
    expr f = Const("f");
    success(F(_,_,f), F(Nat, Real, f), env);
    fails(F(_,Bool,f), env);
    success(F(_,_,Fun({a, Nat},a)), F(Nat,Nat,Fun({a,Nat},a)), env);
}

static void tst9() {
    environment env = mk_toplevel();
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
    expr _ = mk_placholder();
    success(Trans(_,_,_,_,H1,H2), Trans(Bool,a,b,c,H1,H2), env);
    success(Trans(_,_,_,_,Symm(_,_,_,H2),Symm(_,_,_,H1)),
            Trans(Bool,c,b,a,Symm(Bool,b,c,H2),Symm(Bool,a,b,H1)), env);
    success(Symm(_,_,_,Trans(_,_,_,_,Symm(_,_,_,H2),Symm(_,_,_,H1))),
            Symm(Bool,c,a,Trans(Bool,c,b,a,Symm(Bool,b,c,H2),Symm(Bool,a,b,H1))), env);
    env.add_axiom("H3", a);
    expr H3 = Const("H3");
    success(EqTIntro(_, EqMP(_,_,Symm(_,_,_,Trans(_,_,_,_,Symm(_,_,_,H2),Symm(_,_,_,H1))), H3)),
            EqTIntro(c, EqMP(a,c,Symm(Bool,c,a,Trans(Bool,c,b,a,Symm(Bool,b,c,H2),Symm(Bool,a,b,H1))), H3)),
            env);
}

static void tst10() {
    environment env = mk_toplevel();
    expr Nat = Const("Nat");
    env.add_var("Nat", Type());
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
    expr _ = mk_placholder();
    success(Congr2(_,_,_,_,f,H),
            Congr2(Nat, Fun({n,Nat}, vec(n) >> Nat), a, b, f, H), env);
    env.add_var("g", Pi({n, Nat}, vec(n) >> Nat));
    expr g = Const("g");
    env.add_axiom("H2", Eq(f, g));
    expr H2 = Const("H2");
    success(Congr(_,_,_,_,_,_,H2,H),
            Congr(Nat, Fun({n,Nat}, vec(n) >> Nat), f, g, a, b, H2, H), env);
    success(Congr(_,_,_,_,_,_,Refl(_,f),H),
            Congr(Nat, Fun({n,Nat}, vec(n) >> Nat), f, f, a, b, Refl(Pi({n, Nat}, vec(n) >> Nat),f), H), env);
    success(Refl(_,a), Refl(Nat,a), env);
}

static void tst11() {
    environment env;
    expr Nat = Const("Nat");
    env.add_var("Nat", Type());
    expr R   = Const("R");
    env.add_var("R", Type());
    env.add_var("a", Nat);
    expr a   = Const("a");
    expr f   = Const("f");
    env.add_var("f", Nat >> ((R >> Nat) >> R));
    expr x   = Const("x");
    expr y   = Const("y");
    expr z   = Const("z");
    expr _ = mk_placholder();
    success(Fun({{x,_},{y,_}}, f(x, y)),
            Fun({{x,Nat},{y,R >> Nat}}, f(x, y)), env);
    success(Fun({{x,_},{y,_},{z,_}}, Eq(f(x, y), f(x, z))),
            Fun({{x,Nat},{y,R >> Nat},{z,R >> Nat}}, Eq(f(x, y), f(x, z))), env);
    expr A   = Const("A");
    success(Fun({{A,Type()},{x,_},{y,_},{z,_}}, Eq(f(x, y), f(x, z))),
            Fun({{A,Type()},{x,Nat},{y,R >> Nat},{z,R >> Nat}}, Eq(f(x, y), f(x, z))), env);
}

static void tst12() {
    environment env;
    expr A = Const("A");
    expr B = Const("B");
    expr a = Const("a");
    expr b = Const("b");
    expr f = Const("f");
    expr g = Const("g");
    expr Nat = Const("Nat");
    env.add_var("Nat", Type());
    env.add_var("f", Pi({{A,Type()},{a,A},{b,A}}, A));
    env.add_var("g", Nat >> Nat);
    expr _ = mk_placholder();
    success(Fun({{a,_},{b,_}},g(f(_,a,b))),
            Fun({{a,Nat},{b,Nat}},g(f(Nat,a,b))), env);
}

static void tst13() {
    environment env;
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
    env.add_var("f", lst(N>>N) >> Bool);
    expr _ = mk_placholder();
    success(Fun({a,_}, f(cons(_, a, cons(_, a, nil(_))))),
            Fun({a,N>>N}, f(cons(N>>N, a, cons(N>>N, a, nil(N>>N))))), env);
}

static void tst14() {
    environment env;
    expr x = Const("x");
    expr _ = mk_placholder();
    expr omega = mk_app(Fun({x,_}, x(x)), Fun({x,_}, x(x)));
    fails(omega, env);
}

static void tst15() {
    environment env;
    expr B = Const("B");
    expr A = Const("A");
    expr x = Const("x");
    expr f = Const("f");
    expr _ = mk_placholder();
    env.add_var("f", Pi({B, Type()}, B >> B));
    fails(Fun({{x,_}, {A,Type()}}, f(A, x)), env);
    success(Fun({{A,Type()}, {x,_}}, f(A, x)),
            Fun({{A,Type()}, {x,A}}, f(A, x)), env);
    success(Fun({{A,Type()}, {B,Type()}, {x,_}}, f(A, x)),
            Fun({{A,Type()}, {B,Type()}, {x,A}}, f(A, x)), env);
    success(Fun({{A,Type()}, {B,Type()}, {x,_}}, f(B, x)),
            Fun({{A,Type()}, {B,Type()}, {x,B}}, f(B, x)), env);
    success(Fun({{A,Type()}, {B,Type()}, {x,_}}, Eq(f(B, x), f(_,x))),
            Fun({{A,Type()}, {B,Type()}, {x,B}}, Eq(f(B, x), f(B,x))), env);
    success(Fun({{A,Type()}, {B,_}, {x,_}}, Eq(f(B, x), f(_,x))),
            Fun({{A,Type()}, {B,Type()}, {x,B}}, Eq(f(B, x), f(B,x))), env);
    unsolved(Fun({{A,_}, {B,_}, {x,_}}, Eq(f(B, x), f(_,x))), env);
}

static void tst16() {
    environment env = mk_toplevel();
    expr A = Const("A");
    expr B = Const("B");
    expr f = Const("f");
    expr g = Const("g");
    expr x = Const("x");
    expr y = Const("y");
    env.add_var("N", Type());
    env.add_var("f", Pi({A,Type()}, A >> A));
    expr N = Const("N");
    expr _ = mk_placholder();
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
                  Fun({{x,_},{y,_}}, Eq(f(_, x), f(_, y))),
                  Fun({{x,N},{y,Bool}}, True))),
            Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g((N >> (Bool >> Bool)),
                  Fun({{x,N},{y,Bool}}, Eq(f(N, x), f(Bool, y))),
                  Fun({{x,N},{y,Bool}}, True))), env);

    success(Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g(_,
                  Fun({{x,N},{y,_}}, Eq(f(_, x), f(_, y))),
                  Fun({{x,_},{y,Bool}}, True))),
            Fun({g, Pi({A, Type()}, A >> (A >> Bool))},
                g((N >> (Bool >> Bool)),
                  Fun({{x,N},{y,Bool}}, Eq(f(N, x), f(Bool, y))),
                  Fun({{x,N},{y,Bool}}, True))), env);
}

static void tst17() {
    environment env = mk_toplevel();
    expr A = Const("A");
    expr B = Const("B");
    expr C = Const("C");
    expr a = Const("a");
    expr b = Const("b");
    expr eq = Const("eq");
    expr _ = mk_placholder();
    env.add_var("eq", Pi({A, Type()}, A >> (A >> Bool)));
    success(Fun({{A, Type()},{B,Type()},{a,_},{b,B}}, eq(_,a,b)),
            Fun({{A, Type()},{B,Type()},{a,B},{b,B}}, eq(B,a,b)), env);
    success(Fun({{A, Type()},{B,Type()},{a,_},{b,A}}, eq(_,a,b)),
            Fun({{A, Type()},{B,Type()},{a,A},{b,A}}, eq(A,a,b)), env);
    success(Fun({{A, Type()},{B,Type()},{a,A},{b,_}}, eq(_,a,b)),
            Fun({{A, Type()},{B,Type()},{a,A},{b,A}}, eq(A,a,b)), env);
    success(Fun({{A, Type()},{B,Type()},{a,B},{b,_}}, eq(_,a,b)),
            Fun({{A, Type()},{B,Type()},{a,B},{b,B}}, eq(B,a,b)), env);
    success(Fun({{A, Type()},{B,Type()},{a,B},{b,_},{C,Type()}}, eq(_,a,b)),
            Fun({{A, Type()},{B,Type()},{a,B},{b,B},{C,Type()}}, eq(B,a,b)), env);
    fails(Fun({{A, Type()},{B,Type()},{a,_},{b,_},{C,Type()}}, eq(C,a,b)), env);
    success(Fun({{A, Type()},{B,Type()},{a,_},{b,_},{C,Type()}}, eq(B,a,b)),
            Fun({{A, Type()},{B,Type()},{a,B},{b,B},{C,Type()}}, eq(B,a,b)), env);
}

int main() {
    tst17();
    return 0;
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
    tst15();
    tst16();
    return has_violations() ? 1 : 0;
}
