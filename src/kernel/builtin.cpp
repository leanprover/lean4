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
MK_CONSTANT(xtrans_fn, name("xtrans"));
MK_CONSTANT(congr1_fn, name("congr1"));
MK_CONSTANT(congr2_fn, name("congr2"));
MK_CONSTANT(congr_fn, name("congr"));
MK_CONSTANT(eq_mp_fn, name("eq_mp"));
MK_CONSTANT(truth, name("truth"));
MK_CONSTANT(eqt_elim_fn, name("eqt_elim"));
MK_CONSTANT(ext_fn, name("ext"));
MK_CONSTANT(foralle_fn, name("foralle"));
MK_CONSTANT(foralli_fn, name("foralli"));
MK_CONSTANT(domain_inj_fn, name("domain_inj"));
MK_CONSTANT(range_inj_fn, name("range_inj"));

void add_basic_theory(environment & env) {
    env.define_uvar(uvar_name(m_lvl), level() + LEAN_DEFAULT_LEVEL_SEPARATION);
    env.define_uvar(uvar_name(u_lvl), m_lvl + LEAN_DEFAULT_LEVEL_SEPARATION);
    expr p1 = Bool >> Bool;
    expr p2 = Bool >> p1;

    expr A  = Const("A");
    expr a  = Const("a");
    expr b  = Const("b");
    expr c  = Const("c");
    expr H  = Const("H");
    expr H1 = Const("H1");
    expr H2 = Const("H2");
    expr B  = Const("B");
    expr f  = Const("f");
    expr g  = Const("g");
    expr h  = Const("h");
    expr x  = Const("x");
    expr y  = Const("y");
    expr P  = Const("P");
    expr A1 = Const("A1");
    expr B1 = Const("B1");
    expr a1 = Const("a1");

    // and(x, y) = (if bool x y false)
    env.add_definition(and_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, bIf(x, y, True)));
    // or(x, y) = (if bool x true y)
    env.add_definition(or_fn_name, p2, Fun({{x, Bool}, {y, Bool}}, bIf(x, False, y)));
    // not(x) = (if bool x false true)
    env.add_definition(not_fn_name, p1, Fun({x, Bool}, bIf(x, False, True)));

    // forall : Pi (A : Type u), (A -> Bool) -> Bool
    expr A_pred = A >> Bool;
    expr q_type = Pi({A, TypeU}, A_pred >> Bool);
    env.add_var(forall_fn_name, q_type);
    env.add_definition(exists_fn_name, q_type, Fun({{A,TypeU}, {P, A_pred}}, Not(Forall(A, Fun({x, A}, Not(P(x)))))));

    // refl : Pi (A : Type u) (a : A), a = a
    env.add_axiom(refl_fn_name, Pi({{A, TypeU}, {a, A}}, Eq(a, a)));

    // subst : Pi (A : Type u) (P : A -> bool) (a b : A) (H1 : P a) (H2 : a = b), P b
    env.add_axiom(subst_fn_name, Pi({{A, TypeU}, {P, A_pred}, {a, A}, {b, A}, {H1, P(a)}, {H2, Eq(a,b)}}, P(b)));

    // symm : Pi (A : Type u) (a b : A) (H : a = b), b = a :=
    //         Subst A (Fun x : A => x = a) a b (Refl A a) H
    env.add_theorem(symm_fn_name, Pi({{A, TypeU}, {a, A}, {b, A}, {H, Eq(a, b)}}, Eq(b, a)),
                    Fun({{A, TypeU}, {a, A}, {b, A}, {H, Eq(a, b)}},
                        Subst(A, Fun({x, A}, Eq(x,a)), a, b, Refl(A, a), H)));

    // trans: Pi (A: Type u) (a b c : A) (H1 : a = b) (H2 : b = c), a = c :=
    //           Subst A (Fun x : A => a = x) b c H1 H2
    env.add_theorem(trans_fn_name, Pi({{A, TypeU}, {a, A}, {b, A}, {c, A}, {H1, Eq(a, b)}, {H2, Eq(b, c)}}, Eq(a, c)),
                    Fun({{A, TypeU}, {a, A}, {b, A}, {c, A}, {H1, Eq(a,b)}, {H2, Eq(b,c)}},
                        Subst(A, Fun({x, A}, Eq(a, x)), b, c, H1, H2)));


    // xtrans: Pi (A: Type u) (B : Type u) (a : A) (b c : B) (H1 : a = b) (H2 : b = c), a = c :=
    //           Subst B (Fun x : B => a = x) b c H1 H2
    env.add_theorem(xtrans_fn_name, Pi({{A, TypeU}, {B, TypeU}, {a, A}, {b, B}, {c, B}, {H1, Eq(a, b)}, {H2, Eq(b, c)}}, Eq(a, c)),
                    Fun({{A, TypeU}, {B, TypeU}, {a, A}, {b, B}, {c, B}, {H1, Eq(a, b)}, {H2, Eq(b, c)}},
                        Subst(B, Fun({x, B}, Eq(a, x)), b, c, H1, H2)));

    expr piABx = Pi({x, A}, B(x));
    expr A_arrow_u = A >> TypeU;
    // congr1 : Pi (A : Type u) (B : A -> Type u) (f g: Pi (x : A) B x) (a : A) (H : f = g), f a = g a :=
    //          Subst piABx (Fun h : piABx => f a = h a) f g (Refl piABx f) H
    env.add_theorem(congr1_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {a, A}, {H, Eq(f, g)}}, Eq(f(a), g(a))),
                    Fun({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {a, A}, {H, Eq(f, g)}},
                        Subst(piABx, Fun({h, piABx}, Eq(f(a), h(a))), f, g, Refl(piABx, f), H)));

    // congr2 : Pi (A : Type u) (B : A -> Type u) (f : Pi (x : A) B x) (a b : A) (H : a = b), f a = f b :=
    //           Subst A (Fun x : A => f a = f x) a b (Refl A a) H
    env.add_theorem(congr2_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {a, A}, {b, A}, {H, Eq(a, b)}}, Eq(f(a), f(b))),
                    Fun({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {a, A}, {b, A}, {H, Eq(a, b)}},
                        Subst(A, Fun({x, A}, Eq(f(a), f(x))), a, b, Refl(A, a), H)));

    // congr : Pi (A : Type u) (B : A -> Type u) (f g : Pi (x : A) B x) (a b : A) (H1 : f = g) (H2 : a = b), f a = g b :=
    //         xTrans (B a) (B b) (f a) (f b) (g b) (congr2 A B f g b H1) (congr1 A B f a b H2)
    env.add_theorem(congr_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {a, A}, {b, A}, {H1, Eq(f, g)}, {H2, Eq(a, b)}}, Eq(f(a), g(b))),
                    Fun({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {a, A}, {b, A}, {H1, Eq(f, g)}, {H2, Eq(a, b)}},
                        xTrans(B(a), B(b), f(a), f(b), g(b),
                               Congr2(A, B, f, a, b, H2), Congr1(A, B, f, g, b, H1))));

    // eq_mp : Pi (a b: Bool) (H1 : a = b) (H2 : a), b :=
    //          Subst Bool (Fun x : Bool => x) a b H2 H1
    env.add_theorem(eq_mp_fn_name, Pi({{a, Bool}, {b, Bool}, {H1, Eq(a, b)}, {H2, a}}, b),
                    Fun({{a, Bool}, {b, Bool}, {H1, Eq(a, b)}, {H2, a}},
                        Subst(Bool, Fun({x, Bool}, x), a, b, H2, H1)));

    // truth : True := Refl Bool True
    env.add_theorem(truth_name, True, Refl(Bool, True));

    // eqt_elim : Pi (a : Bool) (H : a = True), a := EqMP(True, a, Symm(Bool, a, True, H), Truth)
    env.add_theorem(eqt_elim_fn_name, Pi({{a, Bool}, {H, Eq(a, True)}}, a),
                    Fun({{a, Bool}, {H, Eq(a, True)}},
                        EqMP(True, a, Symm(Bool, a, True, H), Truth)));

    // ext : Pi (A : Type u) (B : A -> Type u) (f g : Pi (x : A) B x) (H : Pi x : A, (f x) = (g x)), f = g
    env.add_axiom(ext_fn_name, Pi({{A, TypeU}, {B, A_arrow_u}, {f, piABx}, {g, piABx}, {H, Pi({x, A}, Eq(f(x), g(x)))}}, Eq(f, g)));

    // foralle : Pi (A : Type u) (P : A -> bool) (H : (forall A P)) (a : A), P a
    env.add_axiom(foralle_fn_name, Pi({{A, TypeU}, {P, A_pred}, {H, mk_forall(A, P)}, {a, A}}, P(a)));
    // foralli : Pi (A : Type u) (P : A -> bool) (H : Pi (x : A), P x), (forall A P)
    env.add_axiom(foralli_fn_name, Pi({{A, TypeU}, {P, A_pred}, {H, Pi({x, A}, P(x))}}, Forall(A, P)));

    // domain_inj : Pi (A A1: Type u) (B : A -> Type u) (B1 : A1 -> Type u) (H : (Pi (x : A), B x) = (Pi (x : A1), B1 x)), A = A1
    expr piA1B1x = Pi({x, A1}, B1(x));
    expr A1_arrow_u = A1 >> TypeU;
    env.add_axiom(domain_inj_fn_name, Pi({{A, TypeU}, {A1, TypeU}, {B, A_arrow_u}, {B1, A1_arrow_u}, {H, Eq(piABx, piA1B1x)}}, Eq(A, A1)));
    // range_inj : Pi (A A1: Type u) (B : A -> Type u) (B1 : A1 -> Type u) (a : A) (a1 : A1) (H : (Pi (x : A), B x) = (Pi (x : A1), B1 x)), (B a) = (B1 a1)
    env.add_axiom(range_inj_fn_name, Pi({{A, TypeU}, {A1, TypeU}, {B, A_arrow_u}, {B1, A1_arrow_u}, {a, A}, {a1, A1}, {H, Eq(piABx, piA1B1x)}}, Eq(B(a), B1(a1))));
}
}
