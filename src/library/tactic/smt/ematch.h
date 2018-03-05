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
    unsigned  m_max_instances{1000};
    unsigned  m_max_generation{10};
};

class ematch_fn;

class ematch_state {
    friend class ematch_fn;
    app_map               m_app_map;
    rb_expr_set           m_instances;
    unsigned              m_num_instances{0};
    bool                  m_max_instances_exceeded{false};
    ematch_config         m_config;
    hinst_lemmas          m_lemmas;
    hinst_lemmas          m_new_lemmas;
public:
    ematch_state(ematch_config const & cfg, hinst_lemmas const & lemmas = hinst_lemmas()):
        m_config(cfg), m_new_lemmas(lemmas) {}

    void internalize(type_context_old & ctx, expr const & e);
    bool max_instances_exceeded() const { return m_max_instances_exceeded; }
    bool save_instance(expr const & e);
    /* Record the fact that the given lemma was instantiated with the given arguments. */
    bool save_instance(expr const & lemma, buffer<expr> const & args);
    app_map const & get_app_map() const { return m_app_map; }
    hinst_lemmas const & get_lemmas() const { return m_lemmas; }
    hinst_lemmas const & get_new_lemmas() const { return m_new_lemmas; }
    void add_lemma(hinst_lemma const & lemma) { m_new_lemmas.insert(lemma); }
    void set_lemmas(hinst_lemmas const & lemmas) { m_lemmas.clear(); m_new_lemmas = lemmas; }
    ematch_config const & get_config() const { return m_config; }
    vm_obj mk_vm_ematch_config() const;
};

struct new_instance {
    expr     m_instance;
    expr     m_proof;
    unsigned m_generation;
};

/* Ematch patterns in lemma with t, and add instances of lemma at result */
void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, expr const & t,
            buffer<new_instance> & result);

/* Ematch patterns in lemma with terms internalized in the ematch_state, and add instances of lemma at result */
void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, bool filter,
            buffer<new_instance> & result);

/* Ematch patterns of lemmas in s.m_lemmas and s.m_new_lemmas with terms internalized in the ematch_state.
   Add instances to result.
   Move s.m_new_lemmas to s.m_lemmas, and increment gmt from cc.
   For s.m_lemmas, only terms with mt >= gmt are considered. */
void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, buffer<new_instance> & result);

/*
structure cc_config :=
(ignore_instances : bool)
(ac               : bool)
(ho_fns           : option (list name))
*/
pair<name_set, congruence_closure::config> to_ho_fns_cc_config(vm_obj const & cfg);
ematch_config to_ematch_config(vm_obj const & cfg);

ematch_state const & to_ematch_state(vm_obj const & o);
vm_obj to_obj(ematch_state const & s);

void initialize_ematch();
void finalize_ematch();
}
