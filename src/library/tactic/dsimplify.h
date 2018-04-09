/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr_maps.h"
#include "library/type_context.h"
#include "library/defeq_canonizer.h"
#include "library/tactic/simp_lemmas.h"

namespace lean {
/*
structure dsimp_config :=
(md                        := reducible)
(max_steps : nat           := default_max_steps)
(canonize_instances : bool := tt)
(canonize_proofs : bool    := ff)
(single_pass : bool        := ff)
(fail_if_unchaged : bool   := tt)
(eta : bool                := ff)
(zeta : bool               := ff)
(beta : bool               := tt)
(proj : bool               := tt)
(iota : bool               := tt)
(unfold_reducible          := ff)
(memoize                   := tt)
*/
struct dsimp_config {
    transparency_mode         m_md;
    unsigned                  m_max_steps;
    bool                      m_canonize_instances;
    bool                      m_single_pass;
    bool                      m_fail_if_unchanged;
    bool                      m_eta;
    bool                      m_zeta;
    bool                      m_beta;
    bool                      m_proj;
    bool                      m_iota;
    bool                      m_unfold_reducible;
    bool                      m_memoize;
    dsimp_config();
    dsimp_config(vm_obj const & o);
};

class dsimplify_core_fn {
protected:
    type_context_old &        m_ctx;
    defeq_canonizer       m_defeq_canonizer;
    expr_map<expr>        m_cache;
    unsigned              m_num_steps;
    bool                  m_need_restart;
    dsimp_config          m_cfg;

    virtual optional<pair<expr, bool>> pre(expr const &);
    virtual optional<pair<expr, bool>> post(expr const &);

    expr visit_macro(expr const & e);
    expr visit_binding(expr const & e);
    expr visit_let(expr const & e);
    expr visit_app(expr const & e);
    expr visit_meta(expr const & e);
    void inc_num_steps();
    expr visit(expr const & e);

public:
    dsimplify_core_fn(type_context_old & ctx, defeq_canonizer::state & s, dsimp_config const & cfg);
    expr operator()(expr e);
    metavar_context const & mctx() const;
};

class dsimplify_fn : public dsimplify_core_fn {
    simp_lemmas_for   m_simp_lemmas;
    name_set          m_to_unfold;
    expr reduce(expr const & e);
    virtual optional<pair<expr, bool>> pre(expr const & e) override;
    virtual optional<pair<expr, bool>> post(expr const & e) override;
public:
    dsimplify_fn(type_context_old & ctx, defeq_canonizer::state & s,
                 simp_lemmas_for const & lemmas, list<name> const & to_unfold, dsimp_config const & cfg);
};

expr reduce_beta_eta_proj_iota(type_context_old & ctx, expr e, bool beta, bool eta, bool proj, bool iota);
optional<expr> unfold_step(type_context_old & ctx, expr const & e, name_set const & to_unfold, bool unfold_reducible);

void initialize_dsimplify();
void finalize_dsimplify();
}
