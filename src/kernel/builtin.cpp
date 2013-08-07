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
            r = mk_app({op, args[i], r});
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
    virtual expr get_type() const { return Type(); }
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
    virtual expr get_type() const { return Bool; }
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

expr mk_bool_value(bool v) {
    static thread_local expr true_val  = mk_value(*(new bool_value_value(true)));
    static thread_local expr false_val = mk_value(*(new bool_value_value(false)));
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

expr mk_type_m() {
    static thread_local expr r = Type(m_lvl);
    return r;
}

expr mk_type_u() {
    static thread_local expr r = Type(u_lvl);
    return r;
}

class if_fn_value : public value {
    expr m_type;
public:
    static char const * g_kind;
    if_fn_value() {
        expr A    = Const("A");
        // Pi (A: Type), bool -> A -> A -> A
        m_type = Pi({A, TypeU}, Bool >> (A >> (A >> A)));
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
    virtual unsigned hash() const { return 27; }
};
char const * if_fn_value::g_kind = "if";

MK_BUILTIN(if_fn, if_fn_value);

class implies_fn_value : public value {
    expr m_type;
public:
    static char const * g_kind;
    implies_fn_value() {
        m_type = Bool >> (Bool >> Bool);
    }
    virtual ~implies_fn_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return m_type; }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const {
        if (num_args == 3) {
            if ((is_bool_value(args[1]) && is_false(args[1])) ||
                (is_bool_value(args[2]) && is_true(args[2]))) {
                r = True;
                return true;
            } else if (is_bool_value(args[1]) && is_bool_value(args[2]) && is_true(args[1]) && is_false(args[2])) {
                r = False;
                return true;
            }
        }
        return false;
    }
    virtual bool operator==(value const & other) const { return other.kind() == kind(); }
    virtual void display(std::ostream & out) const { out << "=>"; }
    virtual format pp() const { return format("=>"); }
    virtual unsigned hash() const { return 23; }
};
char const * implies_fn_value::g_kind = "implies";

MK_BUILTIN(implies_fn, implies_fn_value);
MK_CONSTANT(and_fn,    name("and"));
MK_CONSTANT(or_fn,     name("or"));
MK_CONSTANT(not_fn,    name("not"));
MK_CONSTANT(forall_fn, name("forall"));
MK_CONSTANT(exists_fn, name("exists"));

// Axioms
MK_CONSTANT(mp_fn,          name("MP"));
MK_CONSTANT(discharge_fn,   name("Discharge"));
MK_CONSTANT(refl_fn,        name("Refl"));
MK_CONSTANT(case_fn,        name("Case"));
MK_CONSTANT(subst_fn,       name("Subst"));
MK_CONSTANT(eta_fn,         name("Eta"));
MK_CONSTANT(imp_antisym_fn, name("ImpAntisym"));

void add_basic_theory(environment & env) {
    env.define_uvar(uvar_name(m_lvl), level() + LEAN_DEFAULT_LEVEL_SEPARATION);
    env.define_uvar(uvar_name(u_lvl), m_lvl + LEAN_DEFAULT_LEVEL_SEPARATION);
    expr p1        = Bool >> Bool;
    expr p2        = Bool >> p1;
    expr f         = Const("f");
    expr a         = Const("a");
    expr b         = Const("b");
    expr x         = Const("x");
    expr y         = Const("y");
    expr A         = Const("A");
    expr A_pred    = A >> Bool;
    expr B         = Const("B");
    expr q_type    = Pi({A, TypeU}, A_pred >> Bool);
    expr piABx     = Pi({x, A}, B(x));
    expr A_arrow_u = A >> TypeU;
    expr P         = Const("P");
    expr H         = Const("H");
    expr H1        = Const("H1");
    expr H2        = Const("H2");

    // not(x) = (x => False)
    env.add_definition(not_fn_name, p1, Fun({x, Bool}, Implies(x, False)));

    // or(x, y) = Not(x) => y
    env.add_definition(or_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, Implies(Not(x), y)));

    // and(x, y) = Not(x => Not(y))
    env.add_definition(and_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, Not(Implies(x, Not(y)))));

    // forall : Pi (A : Type u), (A -> Bool) -> Bool
    env.add_definition(forall_fn_name, q_type, Fun({{A, TypeU}, {P, A_pred}}, Eq(P, Fun({x, A}, True))));
    // TODO: introduce epsilon
    env.add_definition(exists_fn_name, q_type, Fun({{A,TypeU}, {P, A_pred}}, Not(Forall(A, Fun({x, A}, Not(P(x)))))));

    // MP : Pi (a b : Bool) (H1 : a => b) (H2 : a), b
    env.add_axiom(mp_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, Implies(a, b)}, {H2, a}}, b));

    // Discharge : Pi (a b : Bool) (H : a -> b), a => b
    env.add_axiom(discharge_fn_name, Pi({{a, Bool}, {b, Bool}, {H, a >> b}}, Implies(a, b)));

    // Refl : Pi (A : Type u) (a : A), a = a
    env.add_axiom(refl_fn_name, Pi({{A, TypeU}, {a, A}}, Eq(a, a)));

    // Case : Pi (P : Bool -> Bool) (H1 : P True) (H2 : P False) (a : Bool), P a
    env.add_axiom(case_fn_name, Pi({{P, Bool >> Bool}, {H1, P(True)}, {H2, P(False)}, {a, Bool}}, P(a)));

    // Subst : Pi (A : Type u) (P : A -> bool) (a b : A) (H1 : P a) (H2 : a = b), P b
    env.add_axiom(subst_fn_name, Pi({{A, TypeU}, {P, A_pred}, {a, A}, {b, A}, {H1, P(a)}, {H2, Eq(a,b)}}, P(b)));

    // Eta : Pi (A : Type u) (B : A -> Type u), f : (Pi x : A, B x), (Fun x : A => f x) = f
    env.add_axiom(eta_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}}, Eq(Fun({x, A}, f(x)), f)));

    // ImpliesAntisym : Pi (a b : Bool) (H1 : a => b) (H2 : b => a), a = b
    env.add_axiom(imp_antisym_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, Implies(a, b)}, {H2, Implies(b, a)}}, Eq(a, b)));
}
}
