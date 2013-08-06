/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "builtin.h"
#include "environment.h"
#include "abstract.h"

#ifndef LEAN_DEFAULT_LEVEL_SEPARATION
#define LEAN_DEFAULT_LEVEL_SEPARATION 512
#endif

namespace lean {

expr mk_bin_op(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return unit;
    } else {
        expr r = args[num_args - 1];
        unsigned i = num_args - 1;
        while (i > 0) {
            --i;
            r = app(op, args[i], r);
        }
        return r;
    }
}

expr mk_bin_op(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_op(op, unit, l.size(), l.begin());
}

class bool_type_value : public value {
public:
    static char const * g_kind;
    virtual ~bool_type_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return type(level()); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const { return other.kind() == kind(); }
    virtual void display(std::ostream & out) const { out << "bool"; }
    virtual format pp() const { return format("bool"); }
    virtual unsigned hash() const { return 17; }
};

char const * bool_type_value::g_kind = "bool";

MK_BUILTIN(bool_type, bool_type_value);

class bool_value_value : public value {
    bool m_val;
public:
    static char const * g_kind;
    bool_value_value(bool v):m_val(v) {}
    virtual ~bool_value_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return bool_type(); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const {
        return other.kind() == kind() && m_val == static_cast<bool_value_value const &>(other).m_val;
    }
    virtual void display(std::ostream & out) const { out << (m_val ? "true" : "false"); }
    virtual format pp() const { return format(m_val ? "true" : "false"); }
    virtual unsigned hash() const { return m_val ? 3 : 5; }
    bool get_val() const { return m_val; }
};

char const * bool_value_value::g_kind = "bool_value";

expr bool_value(bool v) {
    static thread_local expr true_val  = to_expr(*(new bool_value_value(true)));
    static thread_local expr false_val = to_expr(*(new bool_value_value(false)));
    return v ? true_val : false_val;
}

bool is_bool_value(expr const & e) {
    return is_value(e) && to_value(e).kind() == bool_value_value::g_kind;
}

bool to_bool(expr const & e) {
    lean_assert(is_bool_value(e));
    return static_cast<bool_value_value const &>(to_value(e)).get_val();
}

bool is_true(expr const & e) {
    return is_bool_value(e) && to_bool(e);
}

bool is_false(expr const & e) {
    return is_bool_value(e) && !to_bool(e);
}

static level m_lvl(name("m"));
static level u_lvl(name("u"));

expr m_type() {
    static thread_local expr r = type(m_lvl);
    return r;
}

expr u_type() {
    static thread_local expr r = type(u_lvl);
    return r;
}

class if_fn_value : public value {
    expr m_type;
public:
    static char const * g_kind;
    if_fn_value() {
        expr A = constant("A");
        // Pi (A: Type), bool -> A -> A -> A
        m_type = Fun("A", u_type(), arrow(bool_type(), arrow(A, arrow(A, A))));
    }
    virtual ~if_fn_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return m_type; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 5 && is_bool_value(args[2])) {
            if (to_bool(args[2]))
                r = args[3]; // if A true a b  --> a
            else
                r = args[4]; // if A false a b --> b
            return true;
        } if (num_args == 5 && args[3] == args[4]) {
            r = args[3];     // if A c a a --> a
            return true;
        } else {
            return false;
        }
    }
    virtual bool operator==(value const & other) const { return other.kind() == kind(); }
    virtual void display(std::ostream & out) const { out << "if"; }
    virtual format pp() const { return format("if"); }
    virtual unsigned hash() const { return 23; }
};
char const * if_fn_value::g_kind = "if";

MK_BUILTIN(if_fn, if_fn_value);

MK_CONSTANT(and_fn, name("and"));
MK_CONSTANT(or_fn,  name("or"));
MK_CONSTANT(not_fn, name("not"));

MK_CONSTANT(forall_fn, name("forall"));
MK_CONSTANT(exists_fn, name("exists"));

MK_CONSTANT(refl_fn, name("refl"));
MK_CONSTANT(subst_fn, name("subst"));
MK_CONSTANT(symm_fn, name("symm"));
MK_CONSTANT(trans_fn, name("trans"));
MK_CONSTANT(congr_fn, name("congr"));
MK_CONSTANT(ext_fn, name("ext"));
MK_CONSTANT(foralle_fn, name("foralle"));
MK_CONSTANT(foralli_fn, name("foralli"));
MK_CONSTANT(domain_inj_fn, name("domain_inj"));
MK_CONSTANT(range_inj_fn, name("range_inj"));



void add_basic_theory(environment & env) {
    env.define_uvar(uvar_name(m_lvl), level() + LEAN_DEFAULT_LEVEL_SEPARATION);
    env.define_uvar(uvar_name(u_lvl), m_lvl + LEAN_DEFAULT_LEVEL_SEPARATION);
    expr p1 = arrow(bool_type(), bool_type());
    expr p2 = arrow(bool_type(), p1);

    expr A  = constant("A");
    expr a  = constant("a");
    expr b  = constant("b");
    expr c  = constant("a");
    expr H  = constant("H");
    expr H1 = constant("H1");
    expr H2 = constant("H2");
    expr B  = constant("B");
    expr f  = constant("f");
    expr g  = constant("g");
    expr x  = constant("x");
    expr y  = constant("y");
    expr P  = constant("P");
    expr A1 = constant("A1");
    expr B1 = constant("B1");
    expr a1 = constant("a1");

    // and(x, y) = (if bool x y false)
    env.add_definition(and_fn_name, p2, fun(x, bool_type(), fun(y, bool_type(), mk_bool_if(x, y, bool_value(false)))));
    // or(x, y) = (if bool x true y)
    env.add_definition(or_fn_name, p2, fun(x, bool_type(), fun(y, bool_type(),  mk_bool_if(x, bool_value(true), y))));
    // not(x) = (if bool x false true)
    env.add_definition(not_fn_name, p1, fun(x, bool_type(), mk_bool_if(x, bool_value(false), bool_value(true))));

    // forall : Pi (A : Type u), (A -> Bool) -> Bool
    expr A_pred = arrow(A, bool_type());
    expr q_type = Fun(A, u_type(), arrow(A_pred, bool_type()));
    env.add_var(forall_fn_name, q_type);
    env.add_definition(exists_fn_name, q_type, fun(A, u_type(), fun(P, A_pred, mk_not(mk_forall(A, fun(x, A, mk_not(P(x))))))));

    // refl : Pi (A : Type u) (a : A), a = a
    env.add_axiom(refl_fn_name, Fun(A, u_type(), Fun(a, A, eq(a, a))));
    // subst : Pi (A : Type u) (P : A -> bool) (a b : A) (H1 : P a) (H2 : a = b), P b
    env.add_axiom(subst_fn_name, Fun(A, u_type(), Fun(P, A_pred, Fun(a, A, Fun(b, A, Fun(H1, P(a), Fun(H2, eq(a, b), P(b))))))));
    // symm : Pi (A : Type u) (a b : A) (H : a = b), b = a :=
    //         subst A (fun x : A => x = a) a b (refl A a) H
    env.add_definition(symm_fn_name, Fun(A, u_type(), Fun(a, A, Fun(b, A, Fun(H, eq(a, b), eq(b, a))))),
                       fun(A, u_type(), fun(a, A, fun(b, A, fun(H, eq(a, b), app(subst_fn(), A, fun(x, A, eq(x,a)), a, b, app(refl_fn(), A, a), H))))));

    // trans: Pi (A: Type u) (a b c : A) (H1 : a = b) (H2 : b = c), a = c :=
    //           subst A (fun x : A => a = x) b c H1 H2
    env.add_definition(trans_fn_name, Fun(A, u_type(), Fun(a, A, Fun(b, A, Fun(c, A, Fun(H1, eq(a, b), Fun(H2, eq(b, c), eq(a, c))))))),
                       fun(A, u_type(), fun(a, A, fun(b, A, fun(c, A, fun(H1, eq(a, b), fun(H2, eq(b, c), app(subst_fn(), A, fun(x, A, eq(a, x)), b, c, H1, H2))))))));

    // congr : Pi (A : Type u) (B : A -> Type u) (f g : Pi (x : A) B x) (a b : A) (H1 : f = g) (H2 : a = b), f a = g b
    expr piABx = Fun(x, A, B(x));
    expr A_arrow_u = arrow(A, u_type());
    env.add_axiom(congr_fn_name, Fun(A, u_type(), Fun(B, A_arrow_u, Fun(f, piABx, Fun(g, piABx, Fun(a, A, Fun(b, A, Fun(H1, eq(f, g), Fun(H2, eq(a, b), eq(f(a), g(b)))))))))));
    // ext : Pi (A : Type u) (B : A -> Type u) (f g : Pi (x : A) B x) (H : Pi x : A, (f x) = (g x)), f = g
    env.add_axiom(ext_fn_name, Fun(A, u_type(), Fun(B, A_arrow_u, Fun(f, piABx, Fun(g, piABx, Fun(H, Fun(x, A, eq(f(x), g(x))), eq(f, g)))))));

    // foralle : Pi (A : Type u) (P : A -> bool) (H : (forall A P)) (a : A), P a
    env.add_axiom(foralle_fn_name, Fun(A, u_type(), Fun(P, A_pred, Fun(H, mk_forall(A, P), Fun(a, A, P(a))))));
    // foralli : Pi (A : Type u) (P : A -> bool) (H : Pi (x : A), P x), (forall A P)
    env.add_axiom(foralli_fn_name, Fun(A, u_type(), Fun(P, A_pred, Fun(H, Fun(x, A, P(x)), mk_forall(A, P)))));

    // domain_inj : Pi (A A1: Type u) (B : A -> Type u) (B1 : A1 -> Type u) (H : (Pi (x : A), B x) = (Pi (x : A1), B1 x)), A = A1
    expr piA1B1x = Fun(x, A1, B1(x));
    env.add_axiom(domain_inj_fn_name, Fun(A, u_type(), Fun(A1, u_type(), Fun(B, A_arrow_u, Fun(B1, arrow(A1, u_type()), Fun(H, eq(piABx, piA1B1x), eq(A, A1)))))));
    // range_inj : Pi (A A1: Type u) (B : A -> Type u) (B1 : A1 -> Type u) (a : A) (a1 : A1) (H : (Pi (x : A), B x) = (Pi (x : A1), B1 x)), (B a) = (B1 a1)
    env.add_axiom(range_inj_fn_name, Fun(A, u_type(), Fun(A1, u_type(), Fun(B, A_arrow_u, Fun(B1, arrow(A1, u_type()), Fun(a, A, Fun(a1, A1, Fun(H, eq(piABx, piA1B1x), eq(B(a), B1(a1))))))))));
}
}
