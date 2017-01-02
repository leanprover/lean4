/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/discr_tree.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
class smt;

struct smt_config {
    name_set                   m_ho_fns;
    congruence_closure::config m_cc_config;
    ematch_config              m_em_config;
    simp_lemmas                m_simp_lemmas;
};

class smt_goal {
    friend class smt;
    cc_state          m_cc_state;
    ematch_state      m_em_state;
    simp_lemmas       m_simp_lemmas;
public:
    smt_goal(smt_config const & cfg);
    cc_state const & get_cc_state() const { return m_cc_state; }
    simp_lemmas const & get_simp_lemmas() const { return m_simp_lemmas; }
};

class smt {
private:
    type_context &     m_ctx;
    smt_goal &         m_goal;
    congruence_closure m_cc;
public:
    smt(type_context & ctx, smt_goal & g);

    void internalize(expr const & e, bool toplevel);
    void add(expr const & type, expr const & proof);
};

void initialize_smt_state();
void finalize_smt_state();
}
