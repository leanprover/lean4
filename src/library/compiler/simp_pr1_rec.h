/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/** \brief Simplify subterms of the form (pr1 (C.rec ...)) where each minor premise of <tt>C.rec</tt>
    is of the form <tt>(lambda ctx, prod.mk V1 V2)</tt>, and every occurrence of a "recursive argument" r
    in \c V1 is of the form <tt>pr1 r</tt>.

    We use this simplifier because the definitional package is based on a "course of values" recursor (aka C.brec_on).
    However, in many case, the generated definition only accesses the immediate recursive value, and consequently can
    be simplified.

    Example: given, the recursive definition

    definition append {T : Type} : list T → list T → list T
    | []       l := l
    | (h :: s) t := h :: (append s t)

    The definitional package generates (remark: we are hiding implict arguments).

    λ (T : Type) (a : list T),
      list.brec_on a
        (λ (a : list T) (b : list.below a) (a_1 : list T),
           list.cases_on a (λ (b : list.below list.nil), a_1)
             (λ (a_1_1 : T) (a_2 : list T) (b : list.below (list.cons a_1_1 a_2)), list.cons a_1_1 (prod.pr1 b a_1))
             b)

    After unfolding auxiliary recursors and simplifying, we have:

    λ (T : Type) (a x : list T),
      prod.pr1
        (list.rec (λ (a : list T), (a, poly_unit.star))
           (λ (a : T) (a_1 : list T) (v_0 : (list T → list T) × list.below a_1),
              (λ (a_2 : list T),
                (list.cons a (prod.pr1 v_0 a_2), v_0)))
           a)
      x

    Given the term above, the function simp_pr1_rec produces:

    λ (T : Type) (a x : list T),
      list.rec
        (λ (a : list T), a)
        (λ (a : T) (a_1 : list T) (v_0 : list T → list T) (a_2 : list T),
           list.cons a (v_0 a_2))
        a
        x
*/
expr simp_pr1_rec(environment const & env, expr const & e);
}
