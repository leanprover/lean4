/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "test.h"
#include "metavar_env.h"
#include "elaborator.h"
#include "free_vars.h"
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
            return menv.mk_metavar(length(ctx));
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

static void tst1() {
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

static void tst2() {
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

static void tst3() {
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

static void tst4() {
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

static void tst5() {
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

static void tst6() {
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

static void tst7() {
    environment env;
    expr x = Const("x");
    expr _ = mk_placholder();
    expr omega = mk_app(Fun({x,_}, x(x)), Fun({x,_}, x(x)));
    fails(omega, env);
}

static void tst8() {
    environment env;
    expr B = Const("B");
    expr A = Const("A");
    expr x = Const("x");
    expr f = Const("f");
    expr _ = mk_placholder();
    env.add_var("f", Pi({B, Type()}, B >> B));
    success(Fun({{A,Type()}, {B,Type()}, {x,_}}, f(B, x)),
            Fun({{A,Type()}, {B,Type()}, {x,B}}, f(B, x)), env);
    fails(Fun({{x,_}, {A,Type()}}, f(A, x)), env);
    success(Fun({{A,Type()}, {x,_}}, f(A, x)),
            Fun({{A,Type()}, {x,A}}, f(A, x)), env);
    success(Fun({{A,Type()}, {B,Type()}, {x,_}}, f(A, x)),
            Fun({{A,Type()}, {B,Type()}, {x,A}}, f(A, x)), env);
    success(Fun({{A,Type()}, {B,Type()}, {x,_}}, Eq(f(B, x), f(_,x))),
            Fun({{A,Type()}, {B,Type()}, {x,B}}, Eq(f(B, x), f(B,x))), env);
    success(Fun({{A,Type()}, {B,_}, {x,_}}, Eq(f(B, x), f(_,x))),
            Fun({{A,Type()}, {B,Type()}, {x,B}}, Eq(f(B, x), f(B,x))), env);
    unsolved(Fun({{A,_}, {B,_}, {x,_}}, Eq(f(B, x), f(_,x))), env);
}

static void tst9() {
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

static void tst10() {
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


static void tst11() {
    environment env = mk_toplevel();
    expr a  = Const("a");
    expr b  = Const("b");
    expr c  = Const("c");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    env.add_var("a", Bool);
    env.add_var("b", Bool);
    env.add_var("c", Bool);
    expr _ = mk_placholder();
    success(Fun({{H1, Eq(a,b)},{H2,Eq(b,c)}},
                Trans(_,_,_,_,H1,H2)),
            Fun({{H1, Eq(a,b)},{H2,Eq(b,c)}},
                Trans(Bool,a,b,c,H1,H2)),
            env);
    expr H3 = Const("H3");
    success(Fun({{H1, Eq(a,b)},{H2,Eq(b,c)},{H3,a}},
                EqTIntro(_, EqMP(_,_,Symm(_,_,_,Trans(_,_,_,_,Symm(_,_,_,H2),Symm(_,_,_,H1))), H3))),
            Fun({{H1, Eq(a,b)},{H2,Eq(b,c)},{H3,a}},
                EqTIntro(c, EqMP(a,c,Symm(Bool,c,a,Trans(Bool,c,b,a,Symm(Bool,b,c,H2),Symm(Bool,a,b,H1))), H3))),
            env);
    environment env2 = mk_toplevel();
    success(Fun({{a,Bool},{b,Bool},{c,Bool},{H1, Eq(a,b)},{H2,Eq(b,c)},{H3,a}},
                EqTIntro(_, EqMP(_,_,Symm(_,_,_,Trans(_,_,_,_,Symm(_,_,_,H2),Symm(_,_,_,H1))), H3))),
            Fun({{a,Bool},{b,Bool},{c,Bool},{H1, Eq(a,b)},{H2,Eq(b,c)},{H3,a}},
                EqTIntro(c, EqMP(a,c,Symm(Bool,c,a,Trans(Bool,c,b,a,Symm(Bool,b,c,H2),Symm(Bool,a,b,H1))), H3))),
            env2);
    expr A = Const("A");
    success(Fun({{A,Type()},{a,A},{b,A},{c,A},{H1, Eq(a,b)},{H2,Eq(b,c)}},
                Symm(_,_,_,Trans(_,_,_,_,Symm(_,_,_,H2),Symm(_,_,_,H1)))),
            Fun({{A,Type()},{a,A},{b,A},{c,A},{H1, Eq(a,b)},{H2,Eq(b,c)}},
                Symm(A,c,a,Trans(A,c,b,a,Symm(A,b,c,H2),Symm(A,a,b,H1)))),
            env2);
}

void tst12() {
    environment env;
    expr A  = Const("A");
    expr B  = Const("B");
    expr a  = Const("a");
    expr b  = Const("b");
    expr eq = Const("eq");
    expr _ = mk_placholder();
    env.add_var("eq", Pi({A, Type(level()+1)}, A >> (A >> Bool)));
    success(eq(_, Fun({{A, Type()}, {a, _}}, a), Fun({{B, Type()}, {b, B}}, b)),
            eq(Pi({A, Type()}, A >> A), Fun({{A, Type()}, {a, A}}, a), Fun({{B, Type()}, {b, B}}, b)),
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
    return has_violations() ? 1 : 0;
}
