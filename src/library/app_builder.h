/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/type_checker.h"

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
    app_builder(type_checker & tc);
    ~app_builder();
    /** \brief Create an application (d.{_ ... _} _ ... _ args[0] ... args[nargs-1]).
        The missing arguments and universes levels are inferred using type inference.

        \remark The method returns none_expr if: not all arguments can be inferred;
        or constraints are created during type inference; or an exception is thrown
        during type inference.

        \remark This methods uses just higher-order pattern matching.
    */
    optional<expr> mk_app(declaration const & d, unsigned nargs, expr const * args, bool use_cache = true);
    optional<expr> mk_app(name const & n, unsigned nargs, expr const * args, bool use_cache = true);
    optional<expr> mk_app(name const & n, std::initializer_list<expr> const & args, bool use_cache = true);
    optional<expr> mk_app(name const & n, expr const & a1, bool use_cache = true);
    optional<expr> mk_app(name const & n, expr const & a1, expr const & a2, bool use_cache = true);
    optional<expr> mk_app(name const & n, expr const & a1, expr const & a2, expr const & a3, bool use_cache = true);
    /** \brief Create a backtracking point for cached information.
        \remark This method does not invoke tc->push()
    */
    void push();
    /** \brief Restore backtracking point, values cached between this push and the corresponding pop
        are removed from the cache.

        \remark This method does not invoke tc->pop()
    */
    void pop();
};

void open_app_builder(lua_State * L);
}
