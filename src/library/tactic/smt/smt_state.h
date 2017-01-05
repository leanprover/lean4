/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/discr_tree.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
class smt;

struct smt_pre_config {
    simp_lemmas m_simp_lemmas;
    unsigned    m_max_steps;
    bool        m_zeta;
};

struct smt_config {
    name_set       m_ho_fns;
    cc_config      m_cc_config;
    ematch_config  m_em_config;
    smt_pre_config m_pre_config;
    hinst_lemmas   m_em_lemmas;
};

class smt_goal {
    friend class smt;
    cc_state       m_cc_state;
    ematch_state   m_em_state;
    smt_pre_config m_pre_config;
public:
    smt_goal(smt_config const & cfg);
    cc_state const & get_cc_state() const { return m_cc_state; }
    smt_pre_config const & get_pre_config() const { return m_pre_config; }
    void add_lemma(hinst_lemma const & lemma) { m_em_state.add_lemma(lemma); }
};

class smt : public cc_propagation_handler {
private:
    type_context &     m_ctx;
    smt_goal &         m_goal;
    congruence_closure m_cc;

    lbool get_value_core(expr const & e);
    lbool get_value(expr const & e);
    virtual void propagated(unsigned n, expr const * p) override;

public:
    smt(type_context & ctx, smt_goal & g);
    virtual ~smt();

    void internalize(expr const & e);
    void add(expr const & type, expr const & proof);
    void ematch(buffer<expr_pair> & result);

    optional<expr> get_proof(expr const & e);
    bool inconsistent() const { return m_cc.inconsistent(); }
    optional<expr> get_inconsistency_proof() const { return m_cc.get_inconsistency_proof(); }
    optional<expr> get_eq_proof(expr const & lhs, expr const & rhs) const {
        return m_cc.get_eq_proof(lhs, rhs);
    }
};

bool is_smt_goal(vm_obj const & o);
smt_goal const & to_smt_goal(vm_obj const & o);
vm_obj to_obj(smt_goal const & s);

format smt_state_pp(vm_obj const & ss, tactic_state const & ts);

void initialize_smt_state();
void finalize_smt_state();
}
