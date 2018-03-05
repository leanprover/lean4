/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/type_context.h"
#include "library/io_state_stream.h"

namespace lean {
/** \brief Generalized expressions. It is a mechanism for representing
    regular expression and universe polymorphic lemmas.

    A universe polymorphic lemma can be converted into a regular expression
    by instantiating it with fresh universe meta-variables.

    We use the abstraction to provide a uniform API to some tactics. */
struct gexpr {
    bool m_univ_poly;
    expr m_expr;
public:
    gexpr(name const & n):m_univ_poly(true), m_expr(mk_constant(n)) {}
    gexpr(expr const & e):m_univ_poly(false), m_expr(e) {}
    gexpr(environment const & env, name const & n):
        m_univ_poly(env.get(n).get_univ_params()), m_expr(mk_constant(n)) {}

    bool is_universe_polymorphic() const {
        return m_univ_poly;
    }

    /** \brief Convert generalized expression into a regular expression.
        If it is universe polymorphic, we accomplish that by creating
        meta-variables using \c mctx. */
    expr to_expr(type_context_old & ctx) const;

    /** \brief Return "bare" expression (without adding fresh metavariables if universe polymorphic) */
    expr to_bare_expr() const { return m_expr; }

    name const & to_name() const { lean_assert(is_universe_polymorphic()); return const_name(m_expr); }

    friend bool operator==(gexpr const & ge1, gexpr const & ge2);
    friend std::ostream const & operator<<(std::ostream const & out, gexpr const & ge);
};

bool operator==(gexpr const & ge1, gexpr const & ge2);
inline bool operator!=(gexpr const & ge1, gexpr const & ge2) { return !operator==(ge1, ge2); }
std::ostream & operator<<(std::ostream & out, gexpr const & ge);
io_state_stream const & operator<<(io_state_stream const & out, gexpr const & ge);
}
