/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/head_map.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/hinst_lemmas.h"

namespace lean {
typedef rb_expr_tree rb_expr_set;
typedef rb_map<head_index, rb_expr_set, head_index::cmp> app_map;

struct ematch_config {
    unsigned  m_max_instances{0};
};

class ematch_state {
    app_map       m_app_map;
    rb_expr_set   m_instances;
    unsigned      m_num_instances{0};
    bool          m_max_instances_exceeded{false};
    ematch_config m_config;
public:
    ematch_state(ematch_config const & cfg):m_config(cfg) {}

    void internalize(type_context & ctx, expr const & e);
    bool max_instances_exceeded() const { return m_max_instances_exceeded; }
    bool save_instance(expr const & e);
    /* Record the fact that the given lemma was instantiated with the given arguments. */
    bool save_instance(expr const & lemma, buffer<expr> const & args);
    app_map const & get_app_map() const { return m_app_map; }
};

void ematch(type_context & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, expr const & t,
            buffer<expr_pair> & result);

void ematch_all(type_context & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, bool filter,
                buffer<expr_pair> & result);

void initialize_ematch();
void finalize_ematch();
}
