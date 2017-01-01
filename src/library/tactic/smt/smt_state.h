/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
struct smt_config {
    name_set                   m_ho_fns;
    congruence_closure::config m_cc_config;
    ematch_config              m_em_config;
};

class smt {
public:
    struct goal {
        congruence_closure::state  m_cc_state;
        ematch_state               m_em_state;
        goal(smt_config const & cfg);
    };
private:
    type_context &     m_ctx;
    goal &             m_goal;
    congruence_closure m_cc;
public:
    smt(type_context & ctx, goal & g);

    void internalize(expr const & e, bool toplevel);
    void add(expr const & type, expr const & proof);
};

typedef smt::goal smt_goal;

void initialize_smt_state();
void finalize_smt_state();
}
