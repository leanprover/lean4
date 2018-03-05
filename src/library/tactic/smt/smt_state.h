/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
class smt;

struct smt_pre_config {
    name        m_simp_attr;
    simp_lemmas m_simp_lemmas;
    unsigned    m_max_steps;
    bool        m_zeta;
};

struct smt_config {
    name_set       m_ho_fns;
    cc_config      m_cc_config;
    ematch_config  m_em_config;
    smt_pre_config m_pre_config;
    name           m_em_attr;
    hinst_lemmas   m_em_lemmas;
};

typedef std::shared_ptr<smt_config> smt_config_ref;

class smt_goal {
    friend class smt;
    cc_state       m_cc_state;
    ematch_state   m_em_state;
    smt_config_ref m_cfg;
public:
    smt_goal(smt_config_ref const & cfg);
    smt_goal(smt_config const & cfg);
    cc_state const & get_cc_state() const { return m_cc_state; }
    ematch_state const & get_em_state() const { return m_em_state; }
    smt_pre_config const & get_pre_config() const { return m_cfg->m_pre_config; }
    smt_config const & get_config() const { return *m_cfg; }

    void add_lemma(hinst_lemma const & lemma) { m_em_state.add_lemma(lemma); }
    void set_lemmas(hinst_lemmas const & lemmas) { m_em_state.set_lemmas(lemmas); }
};

class smt : public cc_propagation_handler, public cc_normalizer {
private:
    type_context_old &     m_ctx;
    defeq_can_state &  m_dcs;
    smt_goal &         m_goal;
    congruence_closure m_cc;

    lbool get_value_core(expr const & e);
    lbool get_value(expr const & e);
    virtual void propagated(unsigned n, expr const * p) override;
    virtual void new_aux_cc_term(expr const & e) override;
    virtual expr normalize(expr const & e) override;
public:
    smt(type_context_old & ctx, defeq_can_state & dcs, smt_goal & g);
    virtual ~smt();

    void internalize(expr const & e);
    void add(expr const & type, expr const & proof, unsigned gen = 0);
    void ematch(buffer<new_instance> & result);
    void ematch_using(hinst_lemma const & lemma, buffer<new_instance> & result);

    defeq_can_state & dcs() { return m_dcs; }
    smt_pre_config const & get_pre_config() { return m_goal.get_pre_config(); }

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
