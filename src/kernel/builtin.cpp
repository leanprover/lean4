/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"

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
static level m_lvl(name("M"));
static level u_lvl(name("U"));
expr const TypeM = Type(m_lvl);
expr const TypeU = Type(u_lvl);
// =======================================

// =======================================
// Boolean Type
static char const * g_Bool_str = "Bool";
static name g_Bool_name(g_Bool_str);
static format g_Bool_fmt(g_Bool_str);
class bool_type_value : public value {
public:
    virtual ~bool_type_value() {}
    virtual expr get_type() const { return Type(); }
    virtual name get_name() const { return g_Bool_name; }
};
expr const Bool = mk_value(*(new bool_type_value()));
expr mk_bool_type() { return Bool; }
MK_IS_BUILTIN(is_bool, Bool)
// =======================================

// =======================================
// Boolean values True and False
static name g_true_name("true");
static name g_false_name("false");
static name g_true_u_name("\u22A4"); // ⊤
static name g_false_u_name("\u22A5"); // ⊥
/**
   \brief Semantic attachments for Boolean values.
*/
class bool_value_value : public value {
    bool m_val;
public:
    bool_value_value(bool v):m_val(v) {}
    virtual ~bool_value_value() {}
    virtual expr get_type() const { return Bool; }
    virtual name get_name() const { return m_val ? g_true_name : g_false_name; }
    virtual name get_unicode_name() const { return m_val ? g_true_u_name : g_false_u_name; }
    // LCOV_EXCL_START
    virtual bool operator==(value const & other) const {
        // This method is unreachable because there is only one copy of True and False in the system,
        // and they have different hashcodes.
        bool_value_value const * _other = dynamic_cast<bool_value_value const*>(&other);
        return _other && _other->m_val == m_val;
    }
    // LCOV_EXCL_STOP
    bool get_val() const { return m_val; }
};
expr const True  = mk_value(*(new bool_value_value(true)));
expr const False = mk_value(*(new bool_value_value(false)));
expr mk_bool_value(bool v) {
    return v ? True : False;
}
bool is_bool_value(expr const & e) {
    return is_value(e) && dynamic_cast<bool_value_value const *>(&to_value(e)) != nullptr;
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
static name   g_if_name("if");
static format g_if_fmt(g_if_name);
/**
   \brief Semantic attachment for if-then-else operator with type
   <code>Pi (A : Type), Bool -> A -> A -> A</code>
*/
class if_fn_value : public value {
    expr m_type;
    static expr mk_type() {
        expr A    = Const("A");
        // Pi (A: Type), bool -> A -> A -> A
        return Pi({A, TypeU}, Bool >> (A >> (A >> A)));
    }
public:
    if_fn_value():m_type(mk_type()) {}
    virtual ~if_fn_value() {}
    virtual expr get_type() const { return m_type; }
    virtual name get_name() const { return g_if_name; }
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const {
        if (num_args == 5 && is_bool_value(args[2])) {
            if (to_bool(args[2]))
                return some_expr(args[3]); // if A true a b  --> a
            else
                return some_expr(args[4]); // if A false a b --> b
        } else {
            return none_expr();
        }
    }
};
MK_BUILTIN(if_fn, if_fn_value);
MK_IS_BUILTIN(is_if_fn, mk_if_fn());
bool is_if(expr const & n, expr & c, expr & t, expr & e) {
    if (is_if(n)) {
        c = arg(n, 2);
        t = arg(n, 3);
        e = arg(n, 4);
        return true;
    } else {
        return false;
    }
}
// =======================================

MK_CONSTANT(implies_fn, name("implies"));
MK_IS_BINARY_APP(is_implies)
MK_CONSTANT(iff_fn,     name("iff"));
MK_IS_BINARY_APP(is_iff)
MK_CONSTANT(and_fn,     name("and"));
MK_IS_BINARY_APP(is_and)
MK_CONSTANT(or_fn,      name("or"));
MK_IS_BINARY_APP(is_or)
MK_CONSTANT(not_fn,     name("not"));
bool is_not(expr const & e, expr & a) {
    if (is_not(e)) {
        a = arg(e, 1);
        return true;
    } else {
        return false;
    }
}
MK_CONSTANT(forall_fn,  name("forall"));
MK_CONSTANT(exists_fn,  name("exists"));
MK_CONSTANT(Forall_fn,  name("Forall"));
MK_CONSTANT(Exists_fn,  name("Exists"));

MK_CONSTANT(homo_eq_fn, name("eq"));
bool is_homo_eq(expr const & e, expr & lhs, expr & rhs) {
    if (is_homo_eq(e)) {
        lhs = arg(e, 2);
        rhs = arg(e, 3);
        return true;
    } else {
        return false;
    }
}

// Axioms
MK_CONSTANT(mp_fn,          name("MP"));
MK_CONSTANT(discharge_fn,   name("Discharge"));
MK_CONSTANT(case_fn,        name("Case"));
MK_CONSTANT(refl_fn,        name("Refl"));
MK_CONSTANT(subst_fn,       name("Subst"));
MK_CONSTANT(eta_fn,         name("Eta"));
MK_CONSTANT(imp_antisym_fn, name("ImpAntisym"));
MK_CONSTANT(abst_fn,        name("Abst"));

MK_CONSTANT(htrans_fn,      name("HTrans"));
MK_CONSTANT(hsymm_fn,       name("HSymm"));

void import_basic(environment const & env) {
    if (!env->mark_builtin_imported("basic"))
        return;
    env->add_uvar(uvar_name(m_lvl), level() + LEAN_DEFAULT_LEVEL_SEPARATION);
    env->add_uvar(uvar_name(u_lvl), m_lvl + LEAN_DEFAULT_LEVEL_SEPARATION);

    expr p1        = Bool >> Bool;
    expr p2        = Bool >> p1;
    expr f         = Const("f");
    expr g         = Const("g");
    expr a         = Const("a");
    expr b         = Const("b");
    expr c         = Const("c");
    expr x         = Const("x");
    expr y         = Const("y");
    expr A         = Const("A");
    expr A_pred    = A >> Bool;
    expr B         = Const("B");
    expr C         = Const("C");
    expr q_type    = Pi({A, TypeU}, A_pred >> Bool);
    expr piABx     = Pi({x, A}, B(x));
    expr A_arrow_u = A >> TypeU;
    expr P         = Const("P");
    expr H         = Const("H");
    expr H1        = Const("H1");
    expr H2        = Const("H2");

    env->add_builtin(mk_bool_type());
    env->add_builtin(mk_bool_value(true));
    env->add_builtin(mk_bool_value(false));
    env->add_builtin(mk_if_fn());

    // implies(x, y) := if x y True
    env->add_opaque_definition(implies_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, bIf(x, y, True)));

    // iff(x, y) := x = y
    env->add_opaque_definition(iff_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, Eq(x, y)));

    // not(x) := if x False True
    env->add_opaque_definition(not_fn_name, p1, Fun({x, Bool}, bIf(x, False, True)));

    // or(x, y) := Not(x) => y
    env->add_opaque_definition(or_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, Implies(Not(x), y)));

    // and(x, y) := Not(x => Not(y))
    env->add_opaque_definition(and_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, Not(Implies(x, Not(y)))));

    // forall : Pi (A : Type u), (A -> Bool) -> Bool
    env->add_opaque_definition(forall_fn_name, q_type, Fun({{A, TypeU}, {P, A_pred}}, Eq(P, Fun({x, A}, True))));
    // TODO(Leo): introduce epsilon
    env->add_definition(exists_fn_name, q_type, Fun({{A, TypeU}, {P, A_pred}}, Not(Forall(A, Fun({x, A}, Not(P(x)))))));
    // Aliases for forall and exists
    env->add_definition(Forall_fn_name, q_type, Fun({{A, TypeU}, {P, A_pred}}, Forall(A, P)));
    env->add_definition(Exists_fn_name, q_type, Fun({{A, TypeU}, {P, A_pred}}, Exists(A, P)));

    // homogeneous equality
    env->add_definition(homo_eq_fn_name, Pi({{A, TypeU}, {x, A}, {y, A}}, Bool), Fun({{A, TypeU}, {x, A}, {y, A}}, Eq(x, y)));

    // MP : Pi (a b : Bool) (H1 : a => b) (H2 : a), b
    env->add_axiom(mp_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, Implies(a, b)}, {H2, a}}, b));

    // Discharge : Pi (a b : Bool) (H : a -> b), a => b
    env->add_axiom(discharge_fn_name, Pi({{a, Bool}, {b, Bool}, {H, a >> b}}, Implies(a, b)));

    // Case : Pi (P : Bool -> Bool) (H1 : P True) (H2 : P False) (a : Bool), P a
    env->add_axiom(case_fn_name, Pi({{P, Bool >> Bool}, {H1, P(True)}, {H2, P(False)}, {a, Bool}}, P(a)));

    // Refl : Pi (A : Type u) (a : A), a = a
    env->add_axiom(refl_fn_name, Pi({{A, TypeU}, {a, A}}, Eq(a, a)));

    // Subst : Pi (A : Type u) (a b : A) (P : A -> bool) (H1 : P a) (H2 : a = b), P b
    env->add_axiom(subst_fn_name, Pi({{A, TypeU}, {a, A}, {b, A}, {P, A_pred}, {H1, P(a)}, {H2, Eq(a, b)}}, P(b)));

    // Eta : Pi (A : Type u) (B : A -> Type u), f : (Pi x : A, B x), (Fun x : A => f x) = f
    env->add_axiom(eta_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}}, Eq(Fun({x, A}, f(x)), f)));

    // ImpliesAntisym : Pi (a b : Bool) (H1 : a => b) (H2 : b => a), a = b
    env->add_axiom(imp_antisym_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, Implies(a, b)}, {H2, Implies(b, a)}}, Eq(a, b)));

    // Abst : Pi (A : Type u) (B : A -> Type u), f g : (Pi x : A, B x), H : (Pi x : A, (f x) = (g x)), f = g
    env->add_axiom(abst_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {H, Pi(x, A, Eq(f(x), g(x)))}}, Eq(f, g)));

    // HSymm : Pi (A B : Type u) (a : A) (b : B) (H1 : a = b), b = a
    env->add_axiom(hsymm_fn_name, Pi({{A, TypeU}, {B, TypeU}, {a, A}, {b, B}, {H1, Eq(a, b)}}, Eq(b, a)));

    // HTrans : Pi (A B C: Type u) (a : A) (b : B) (c : C) (H1 : a = b) (H2 : b = c), a = c
    env->add_axiom(htrans_fn_name, Pi({{A, TypeU}, {B, TypeU}, {C, TypeU}, {a, A}, {b, B}, {c, C}, {H1, Eq(a, b)}, {H2, Eq(b, c)}}, Eq(a, c)));
}
}
