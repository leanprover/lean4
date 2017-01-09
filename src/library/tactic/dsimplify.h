/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/defeq_canonizer.h"
#include "library/tactic/simp_lemmas.h"

namespace lean {
class dsimplify_core_fn {
protected:
    type_context &        m_ctx;
    defeq_canonizer       m_defeq_canonizer;
    expr_struct_map<expr> m_cache;
    unsigned              m_num_steps;
    bool                  m_need_restart;

    unsigned              m_max_steps;
    bool                  m_visit_instances;

    virtual optional<pair<expr, bool>> pre(expr const &);
    virtual optional<pair<expr, bool>> post(expr const &);

    expr visit_macro(expr const & e);
    expr visit_binding(expr const & e);
    expr visit_let(expr const & e);
    expr visit_app(expr const & e);
    void inc_num_steps();
    expr visit(expr const & e);

public:
    dsimplify_core_fn(type_context & ctx, defeq_canonizer::state & s, unsigned max_steps, bool visit_instances);
    expr operator()(expr e);
    metavar_context const & mctx() const;
};

class dsimplify_fn : public dsimplify_core_fn {
    simp_lemmas_for   m_simp_lemmas;
    bool              m_use_eta;
    transparency_mode m_md;
    expr whnf(expr const & e);
    virtual optional<pair<expr, bool>> pre(expr const & e) override;
    virtual optional<pair<expr, bool>> post(expr const & e) override;
public:
    dsimplify_fn(type_context & ctx, defeq_canonizer::state & s,
                 unsigned max_steps, bool visit_instances, simp_lemmas_for const & lemmas,
                 bool use_eta, transparency_mode md = transparency_mode::Reducible);
};

void initialize_dsimplify();
void finalize_dsimplify();
}
