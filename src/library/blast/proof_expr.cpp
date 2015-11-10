/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/replace_visitor.h"
#include "library/blast/blast.h"
#include "library/blast/proof_expr.h"

namespace lean {
namespace blast {
expr to_proof_expr(expr const & e) {
    return e;
}

struct unfold_hypotheses_ge_fn : public replace_visitor {
    state const &      m_state;
    unsigned           m_depth;

    unfold_hypotheses_ge_fn(state const & s, unsigned d):
        m_state(s), m_depth(d) {}

    virtual expr visit_local(expr const & e) {
        if (is_href(e)) {
            hypothesis const * h = m_state.get_hypothesis_decl(e);
            if (h->get_proof_depth() >= m_depth && h->get_value()) {
                return visit(*h->get_value());
            }
        }
        return replace_visitor::visit_local(e);
    }
};

expr unfold_hypotheses_ge(state const & s, expr const & pr, unsigned d) {
    return unfold_hypotheses_ge_fn(s, d)(pr);
}

expr mk_proof_lambda(state const & s, list<expr> const & hs, expr const & pr) {
    return s.mk_lambda(hs, pr);
}

expr mk_proof_app(name const & fname, unsigned nargs, expr const * args) {
    return get_app_builder().mk_app(fname, nargs, args);
}

expr mk_proof_app(expr const & f, unsigned nargs, expr const * args) {
    return mk_app(f, nargs, args);
}
}}
