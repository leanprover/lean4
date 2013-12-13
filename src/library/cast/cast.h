/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief Type Cast. It has type <tt>Pi (A : Type u) (B : Type u) (H : A = B) (a : A), B</tt> */
expr mk_cast_fn();
/** \brief Return the term (cast A B H a) */
inline expr mk_cast(expr const & A, expr const & B, expr const & H, expr const & a) { return mk_app(mk_cast_fn(), A, B, H, a); }
inline expr Cast(expr const & A, expr const & B, expr const & H, expr const & a) { return mk_cast(A, B, H, a); }

/** \brief Domain Injectivity.
    It has type <tt>Pi (A A': Type u) (B : A -> Type u) (B' : A' -> Type u) (H : (Pi x : A, B x) = (Pi x : A', B' x)), A = A' </tt>
*/
expr mk_dom_inj_fn();
/** \brief Return the term (DomInj A A' B B' H) */
inline expr mk_dom_inj(expr const & A, expr const & Ap, expr const & B, expr const & Bp, expr const & H) {
    return mk_app({mk_dom_inj_fn(), A, Ap, B, Bp, H});
}
inline expr DomInj(expr const & A, expr const & Ap, expr const & B, expr const & Bp, expr const & H) {
    return mk_dom_inj(A, Ap, B, Bp, H);
}

/** \brief Range Injectivity.
    It has type <tt>Pi (A A': Type u) (B : A -> Type u) (B' : A' -> Type u) (H : (Pi x : A, B x) = (Pi x : A', B' x)) (a : A),
                       B a = B' (cast A A' (DomInj A A' B B' H) a)</tt>
*/
expr mk_ran_inj_fn();
/** \brief Return the term (RanInj A A' B B' H) */
inline expr mk_ran_inj(expr const & A, expr const & Ap, expr const & B, expr const & Bp, expr const & H, expr const & a) {
    return mk_app({mk_ran_inj_fn(), A, Ap, B, Bp, H, a});
}
inline expr RanInj(expr const & A, expr const & Ap, expr const & B, expr const & Bp, expr const & H, expr const & a) {
    return mk_ran_inj(A, Ap, B, Bp, H, a);
}

class environment;
/** \brief Import type "casting" library */
void import_cast(environment const & env);
}
