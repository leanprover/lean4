/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/builtin.h"
#include "kernel/instantiate.h"
#include "library/basic_thms.h"
#include "library/cast/cast.h"

namespace lean {
// Cast builtin operator
MK_CONSTANT(cast_fn,      name("cast"));
MK_CONSTANT(cast_eq_fn,   name("CastEq"));
MK_CONSTANT(cast_app_fn,  name("CastApp"));
MK_CONSTANT(dom_inj_fn,   name("DomInj"));
MK_CONSTANT(ran_inj_fn,   name("RanInj"));

void import_cast(environment const & env) {
    if (!env->mark_builtin_imported("cast"))
        return;
    expr x         = Const("x");
    expr A         = Const("A");
    expr Ap        = Const("A'");
    expr B         = Const("B");
    expr Bp        = Const("B'");
    expr piABx     = Pi({x, A}, B(x));
    expr piApBpx   = Pi({x, Ap}, Bp(x));
    expr H         = Const("H");
    expr H1        = Const("H1");
    expr H2        = Const("H2");
    expr a         = Const("a");
    expr b         = Const("b");
    expr f         = Const("f");

    env->add_var(cast_fn_name, Pi({{A, TypeU}, {B, TypeU}}, Eq(A, B) >> (A >> B)));

    // DomInj : Pi (A A': Type u) (B : A -> Type u) (B' : A' -> Type u) (H : (Pi x : A, B x) = (Pi x : A', B' x)), A = A'
    env->add_axiom(dom_inj_fn_name, Pi({{A, TypeU}, {Ap, TypeU}, {B, A >> TypeU}, {Bp, Ap >> TypeU}, {H, Eq(piABx, piApBpx)}}, Eq(A, Ap)));

    // RanInj : Pi (A A': Type u) (B : A -> Type u) (B' : A' -> Type u) (H : (Pi x : A, B x) = (Pi x : A', B' x)) (a : A),
    //                     B a = B' (cast A A' (DomInj A A' B B' H) a)
    env->add_axiom(ran_inj_fn_name, Pi({{A, TypeU}, {Ap, TypeU}, {B, A >> TypeU}, {Bp, Ap >> TypeU}, {H, Eq(piABx, piApBpx)}, {a, A}},
                                       Eq(B(a), Bp(Cast(A, Ap, DomInj(A, Ap, B, Bp, H), a)))));

    // CastEq : Pi (A B : Type u) (H : A == B) (x : A), x == (cast A B H x)
    env->add_axiom(cast_eq_fn_name, Pi({{A, TypeU}, {B, TypeU}, {H, Eq(A, B)}, {x, A}}, Eq(x, Cast(A, B, H, x))));

    // CastApp : Pi (A A': Type u) (B : A -> Type u) (B' : A' -> Type u) (H1 : (Pi x : A, B x) = (Pi x : A', B' x)) (H2 : A = A')
    //              (f : Pi x : A, B x) (x : A),  Cast(Pi(x : A, B x), Pi(x : A', B' x), H1, f)(Cast(A, A', H2, x)) ==  f(x)
    env->add_axiom(cast_app_fn_name, Pi({{A, TypeU},
                    {Ap, TypeU}, {B, A >> TypeU}, {Bp, Ap >> TypeU}, {H1, Eq(piABx, piApBpx)}, {H2, Eq(A, Ap)}, {f, piABx}, {x, A}},
            Eq(Cast(piABx, piApBpx, H1, f)(Cast(A, Ap, H2, x)), f(x))));
}
}
