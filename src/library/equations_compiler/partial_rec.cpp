/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/equations_compiler/structural_rec.h"

namespace lean {
struct partial_rec_fn {
    environment      m_env;
    elaborator &     m_elab;
    metavar_context  m_mctx;
    local_context    m_lctx;

    expr             m_ref;
    equations_header m_header;

    partial_rec_fn(environment const & env, elaborator & elab,
                   metavar_context const & mctx, local_context const & lctx):
        m_env(env), m_elab(elab), m_mctx(mctx), m_lctx(lctx) {
    }

    expr add_fuel_param(expr const & eqns) {
        // TODO(Leo):
        return eqns;
    }

    list<expr> add_some_fuel(list<expr> const & fns) {
        // TODO(Leo):
        return fns;
    }

    eqn_compiler_result operator()(expr const & eqns) {
        m_ref         = eqns;
        m_header      = get_equations_header(eqns);
        // TODO(Leo): if it mutual recursion, then we need to "pack" functions, and then add auxiliary "fuel" parameter.
        expr new_eqns = add_fuel_param(eqns);
        optional<eqn_compiler_result> R = try_structural_rec(m_env, m_elab, m_mctx, m_lctx, new_eqns);
        if (!R)
            throw generic_exception(m_ref, "failed to compile partial definition, structural recursion failed after adding fuel");
        // TODO(Leo): if it is mutual recursion, then we need to "unpack" result, and then add default "fuel".
        list<expr> fns = add_some_fuel(R->m_fns);
        return eqn_compiler_result({ fns, R->m_counter_examples });
    }
};

eqn_compiler_result partial_rec(environment & env, elaborator & elab,
                                metavar_context & mctx, local_context const & lctx,
                                expr const & eqns) {
    return partial_rec_fn(env, elab, mctx, lctx)(eqns);
}
}
