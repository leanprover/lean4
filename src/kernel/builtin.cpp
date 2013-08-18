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
expr mk_bin_rop(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
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
expr mk_bin_rop(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_rop(op, unit, l.size(), l.begin());
}

expr mk_bin_lop(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return unit;
    } else {
        expr r = args[0];
        for (unsigned i = 1; i < num_args; i++) {
            r = mk_app({op, r, args[i]});
        }
        return r;
    }
}
expr mk_bin_lop(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_lop(op, unit, l.size(), l.begin());
}


// =======================================
// Bultin universe variables m and u
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
// =======================================

// =======================================
// Boolean Type
static char const * g_Bool_str = "Bool";
static format g_Bool_fmt(g_Bool_str);
class bool_type_value : public value {
public:
    static char const * g_kind;
    virtual ~bool_type_value() {}
    char const * kind() const { return g_kind; }
    virtual expr get_type() const { return Type(); }
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const { return false; }
    virtual bool operator==(value const & other) const { return other.kind() == kind(); }
    virtual void display(std::ostream & out) const { out << g_Bool_str; }
    virtual format pp() const { return g_Bool_fmt; }
    virtual unsigned hash() const { return 17; }
};
char const * bool_type_value::g_kind = g_Bool_str;
MK_BUILTIN(bool_type, bool_type_value);
// =======================================

// =======================================
// Boolean values True and False
static char const * g_true_str  = "\u22A4";
static char const * g_false_str = "\u22A5";
static format g_true_fmt(g_true_str);
static format g_false_fmt(g_false_str);
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
    virtual void display(std::ostream & out) const { out << (m_val ? g_true_str : g_false_str); }
    virtual format pp() const { return m_val ? g_true_fmt : g_false_fmt; }
    virtual unsigned hash() const { return m_val ? 3 : 5; }
    bool get_val() const { return m_val; }
};
char const * bool_value_value::g_kind = "BoolValue";
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
// =======================================

// =======================================
// If-then-else builtin operator
static name   g_ite_name("ite");
static format g_ite_fmt(g_ite_name);
class ite_fn_value : public value {
    expr m_type;
public:
    static char const * g_kind;
    ite_fn_value() {
        expr A    = Const("A");
        // Pi (A: Type), bool -> A -> A -> A
        m_type = Pi({A, TypeU}, Bool >> (A >> (A >> A)));
    }
    virtual ~ite_fn_value() {}
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
    virtual void display(std::ostream & out) const { out << g_ite_name; }
    virtual format pp() const { return g_ite_fmt; }
    virtual unsigned hash() const { return 27; }
};
char const * ite_fn_value::g_kind = "ite";
MK_BUILTIN(ite_fn, ite_fn_value);
// =======================================

MK_CONSTANT(if_fn,      name("if"));
MK_CONSTANT(implies_fn, name("implies"));
MK_CONSTANT(iff_fn,     name("iff"));
MK_CONSTANT(and_fn,     name("and"));
MK_CONSTANT(or_fn,      name("or"));
MK_CONSTANT(not_fn,     name("not"));
MK_CONSTANT(forall_fn,  name("forall"));
MK_CONSTANT(exists_fn,  name("exists"));

// Axioms
MK_CONSTANT(mp_fn,          name("MP"));
MK_CONSTANT(discharge_fn,   name("Discharge"));
MK_CONSTANT(refl_fn,        name("Refl"));
MK_CONSTANT(case_fn,        name("Case"));
MK_CONSTANT(subst_fn,       name("Subst"));
MK_CONSTANT(eta_fn,         name("Eta"));
MK_CONSTANT(imp_antisym_fn, name("ImpAntisym"));

void add_basic_theory(environment & env) {
    env.add_uvar(uvar_name(m_lvl), level() + LEAN_DEFAULT_LEVEL_SEPARATION);
    env.add_uvar(uvar_name(u_lvl), m_lvl + LEAN_DEFAULT_LEVEL_SEPARATION);
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
    expr ite       = mk_ite_fn();

    // if(A, x, y, z) := ite A x y z
    env.add_definition(if_fn_name, to_value(ite).get_type(), ite);

    // implies(x, y) := ite x y True
    env.add_definition(implies_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, bIf(x, y, True)));

    // iff(x, y) := x = y
    env.add_definition(iff_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, Eq(x, y)));

    // not(x) := ite x False True
    env.add_definition(not_fn_name, p1, Fun({x, Bool}, bIf(x, False, True)));

    // or(x, y) := Not(x) => y
    env.add_definition(or_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, Implies(Not(x), y)));

    // and(x, y) := Not(x => Not(y))
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

    // Subst : Pi (A : Type u) (a b : A) (P : A -> bool) (H1 : P a) (H2 : a = b), P b
    env.add_axiom(subst_fn_name, Pi({{A, TypeU}, {a, A}, {b, A}, {P, A_pred}, {H1, P(a)}, {H2, Eq(a,b)}}, P(b)));

    // Eta : Pi (A : Type u) (B : A -> Type u), f : (Pi x : A, B x), (Fun x : A => f x) = f
    env.add_axiom(eta_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}}, Eq(Fun({x, A}, f(x)), f)));

    // ImpliesAntisym : Pi (a b : Bool) (H1 : a => b) (H2 : b => a), a = b
    env.add_axiom(imp_antisym_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, Implies(a, b)}, {H2, Implies(b, a)}}, Eq(a, b)));
}
}
