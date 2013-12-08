/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/builtin.h"
#include "library/basic_thms.h"
#include "library/cast/cast.h"

namespace lean {
// Cast builtin operator
static name   g_cast_name("Cast");
static format g_cast_fmt(g_cast_name);
expr mk_Cast_fn();
class cast_fn_value : public value {
    expr m_type;
public:
    cast_fn_value() {
        expr A    = Const("A");
        expr B    = Const("B");
        // Cast: Pi (A : Type u) (B : Type u) (H : A = B) (a : A), B
        m_type = Pi({{A, TypeU}, {B, TypeU}}, Eq(A, B) >> (A >> B));
    }
    virtual ~cast_fn_value() {}
    virtual expr get_type() const { return m_type; }
    virtual name get_name() const { return g_cast_name; }
    virtual optional<expr> normalize(unsigned num_as, expr const * as) const {
        if (num_as > 4 && as[1] == as[2]) {
            // Cast T T H a == a
            if (num_as == 5)
                return some(as[4]);
            else
                return some(mk_app(num_as - 4, as + 4));
        } else if (is_app(as[4]) &&
                   arg(as[4], 0) == mk_Cast_fn() &&
                   num_args(as[4]) == 5 &&
                   as[1] == arg(as[4], 2)) {
            // Cast T1 T2 H1 (Cast T3 T1 H2 a) == Cast T3 T2 (Trans H1 H2) a
            expr const & nested = as[4];
            expr const & T1 = as[1];
            expr const & T2 = as[2];
            expr const & T3 = arg(nested, 1);
            expr const & H1 = as[3];
            expr const & H2 = arg(nested, 3);
            expr const & a  = arg(nested, 4);
            expr c = Cast(T3, T2, Trans(TypeU, T3, T1, T2, H1, H2), a);
            if (num_as == 5) {
                return optional<expr>(c);
            } else {
                buffer<expr> new_as;
                new_as.push_back(c);
                new_as.append(num_as - 5, as + 5);
                return optional<expr>(mk_app(new_as));
            }
        } else if (num_as > 5 && is_pi(as[1]) && is_pi(as[2])) {
            // cast T1 T2 H f a_1 ... a_k
            // Propagate application over cast.
            // Remark: we check if T1 is a Pi to prevent non-termination
            // For example, H can be a bogus hypothesis that shows
            // that A == A -> A

            // Since T1 and T2 are Pi's, we decompose them
            expr const & T1  = as[1]; // Pi x : A1, B1
            expr const & T2  = as[2]; // Pi x : A2, B2
            expr const & H   = as[3];
            expr const & f   = as[4];
            expr const & a_1 = as[5]; // has type A2
            expr const & A1  = abst_domain(T1);
            expr const & B1  = abst_body(T1);
            expr const & A2  = abst_domain(T2);
            expr const & B2  = abst_body(T2);
            expr B1f         = mk_lambda(abst_name(T1), A1, B1);
            expr B2f         = mk_lambda(abst_name(T2), A2, B2);
            expr A1_eq_A2    = DomInj(A1, A2, B1f, B2f, H);
            name t("t");
            expr A2_eq_A1    = Symm(TypeU, A1, A2, A1_eq_A2);
            expr a_1p        = Cast(A2, A1, A2_eq_A1, a_1);
            expr fa_1        = f(a_1p);
            // Cast fa_1 back to B2 since the type of cast T1 T2 H f a_1
            // is in B2 a_1p
            expr B1_eq_B2_at_a_1p = RanInj(A1, A2, B1f, B2f, H, a_1p);
            expr fa_1_B2     = Cast(B1, B2, B1_eq_B2_at_a_1p, fa_1);
            if (num_as == 6) {
                return optional<expr>(fa_1_B2);
            } else {
                buffer<expr> new_as;
                new_as.push_back(fa_1_B2);
                new_as.append(num_as - 6, as + 6);
                return optional<expr>(mk_app(new_as));
            }
        } else {
            return optional<expr>();
        }
    }
};
MK_BUILTIN(Cast_fn,     cast_fn_value);
MK_CONSTANT(cast_fn,    name("cast"));
MK_CONSTANT(dom_inj_fn, name("DomInj"));
MK_CONSTANT(ran_inj_fn, name("RanInj"));

void import_cast(environment & env) {
    if (!env.mark_builtin_imported("cast"))
        return;
    expr x         = Const("x");
    expr A         = Const("A");
    expr Ap        = Const("A'");
    expr B         = Const("B");
    expr Bp        = Const("B'");
    expr piABx     = Pi({x, A}, B(x));
    expr piApBpx   = Pi({x, Ap}, Bp(x));
    expr H         = Const("H");
    expr a         = Const("a");
    expr b         = Const("b");

    env.add_builtin(mk_Cast_fn());

    // Alias for Cast operator. We create the alias to be able to mark
    // implicit arguments.
    env.add_definition(cast_fn_name, Pi({{A, TypeU}, {B, TypeU}}, Eq(A, B) >> (A >> B)), mk_Cast_fn());

    // DomInj : Pi (A A': Type u) (B : A -> Type u) (B' : A' -> Type u) (H : (Pi x : A, B x) = (Pi x : A', B' x)), A = A'
    env.add_axiom(dom_inj_fn_name, Pi({{A, TypeU}, {Ap, TypeU}, {B, A >> TypeU}, {Bp, Ap >> TypeU}, {H, Eq(piABx, piApBpx)}}, Eq(A, Ap)));

    // RanInj : Pi (A A': Type u) (B : A -> Type u) (B' : A' -> Type u) (H : (Pi x : A, B x) = (Pi x : A', B' x)) (a : A),
    //                     B a = B' (cast A A' (DomInj A A' B B' H) a)
    env.add_axiom(ran_inj_fn_name, Pi({{A, TypeU}, {Ap, TypeU}, {B, A >> TypeU}, {Bp, Ap >> TypeU}, {H, Eq(piABx, piApBpx)}, {a, A}},
                                      Eq(B(a), Bp(Cast(A, Ap, DomInj(A, Ap, B, Bp, H), a)))));
}
}
