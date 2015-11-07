/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/reducible.h"
#include "library/tmp_type_context.h"

namespace lean {
/** \brief Helper for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
        rel.{l_1 l_2} : Pi (A : Type.{l_1}) (B : A -> Type.{l_2}), (Pi x : A, B x) -> (Pi x : A, B x) -> , Prop
        nat     : Type.{1}
        real    : Type.{1}
        vec.{l} : Pi (A : Type.{l}) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    then
        builder.mk_app(rel, f, g)
    returns the application
        rel.{1 2} nat (fun n : nat, vec real n) f g
*/
class app_builder {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    app_builder(environment const & env, io_state const & ios, reducible_behavior b = UnfoldReducible);
    app_builder(environment const & env, reducible_behavior b = UnfoldReducible);
    app_builder(tmp_type_context & ctx);
    ~app_builder();

    /** \brief Create an application (d.{_ ... _} _ ... _ args[0] ... args[nargs-1]).
        The missing arguments and universes levels are inferred using type inference.

        \remark The method returns none_expr if: not all arguments can be inferred;
        or constraints are created during type inference; or an exception is thrown
        during type inference.

        \remark This methods uses just higher-order pattern matching.
    */
    optional<expr> mk_app(name const & c, unsigned nargs, expr const * args);

    optional<expr> mk_app(name const & c, std::initializer_list<expr> const & args) {
        return mk_app(c, args.size(), args.begin());
    }

    optional<expr> mk_app(name const & c, expr const & a1) {
        return mk_app(c, {a1});
    }

    optional<expr> mk_app(name const & c, expr const & a1, expr const & a2) {
        return mk_app(c, {a1, a2});
    }

    optional<expr> mk_app(name const & c, expr const & a1, expr const & a2, expr const & a3) {
        return mk_app(c, {a1, a2, a3});
    }

    optional<expr> mk_app(name const & c, unsigned mask_sz, bool const * mask, expr const * args);

    /** \brief Similar to mk_app(n, lhs, rhs), but handles eq and iff more efficiently. */
    optional<expr> mk_rel(name const & n, expr const & lhs, expr const & rhs);
    optional<expr> mk_eq(expr const & lhs, expr const & rhs);
    optional<expr> mk_iff(expr const & lhs, expr const & rhs);

    /** \brief Similar a reflexivity proof for the given relation */
    optional<expr> mk_refl(name const & relname, expr const & a);
    optional<expr> mk_eq_refl(expr const & a);
    optional<expr> mk_iff_refl(expr const & a);

    /** \brief Similar a symmetry proof for the given relation */
    optional<expr> mk_symm(name const & relname, expr const & H);
    optional<expr> mk_eq_symm(expr const & H);
    optional<expr> mk_iff_symm(expr const & H);

    /** \brief Similar a transitivity proof for the given relation */
    optional<expr> mk_trans(name const & relname, expr const & H1, expr const & H2);
    optional<expr> mk_eq_trans(expr const & H1, expr const & H2);
    optional<expr> mk_iff_trans(expr const & H1, expr const & H2);

    /** \brief Create a (non-dependent) eq.rec application.
        C is the motive. The expected types for C, H1 and H2 are
             C : A -> Type
             H1 : C a
             H2 : a = b
        The resultant application is
             @eq.rec A a C H1 b H2
        In the HoTT library, we actually create an eq.nrec application
        since eq.rec is a dependent eliminator in HoTT. */
    optional<expr> mk_eq_rec(expr const & C, expr const & H1, expr const & H2);

    /** \brief Create a (dependent) eq.drec application.
        C is the motive. The expected types for C, H1 and H2 are
             C : Pi (x : A), a = x -> Type
             H1 : C a (eq.refl a)
             H2 : a = b
        The resultant application is
             @eq.drec A a C H1 b H2
        In the HoTT library, we actually create an eq.rec application
        because eq.rec is a dependent eliminator in HoTT. */
    optional<expr> mk_eq_drec(expr const & C, expr const & H1, expr const & H2);

    optional<expr> mk_congr_arg(expr const & f, expr const & H);
    optional<expr> mk_congr_fun(expr const & H, expr const & a);
    optional<expr> mk_congr(expr const & H1, expr const & H2);

    /** \brief Create (@sorry type) */
    optional<expr> mk_sorry(expr const & type);

    /** \brief Set the local instances. This method is relevant when we want to expose local class instances
        to the app_builder.

        \remark When the constructor app_builder(tmp_type_context & ctx) is used
        the initialization can be performed outside. */
    void set_local_instances(list<expr> const & insts);
};
}
