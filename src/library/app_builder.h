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
};
}
