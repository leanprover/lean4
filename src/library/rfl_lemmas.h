/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <memory>
#include "kernel/environment.h"
#include "library/head_map.h"

namespace lean {
class rfl_lemma {
    name                m_id;
    levels              m_umetas;
    list<expr>          m_emetas;
    list<bool>          m_instances;

    expr                m_lhs;
    expr                m_rhs;
    unsigned            m_priority;
public:
    rfl_lemma() {}
    rfl_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
              list<bool> const & instances, expr const & lhs, expr const & rhs, unsigned priority);

    name const & get_id() const { return m_id; }
    unsigned get_num_umeta() const { return length(m_umetas); }
    unsigned get_num_emeta() const { return length(m_emetas); }

    /** \brief Return a list containing the expression metavariables in reverse order. */
    list<expr> const & get_emetas() const { return m_emetas; }

    /** \brief Return a list of bools indicating whether or not each expression metavariable
        in <tt>get_emetas()</tt> is an instance. */
    list<bool> const & get_instances() const { return m_instances; }

    expr const & get_lhs() const { return m_lhs; }
    expr const & get_rhs() const { return m_rhs; }

    unsigned get_priority() const { return m_priority; }
    format pp(formatter const & fmt) const;
};

bool operator==(rfl_lemma const & sl1, rfl_lemma const & sl2);
inline bool operator!=(rfl_lemma const & sl1, rfl_lemma const & sl2) { return !operator==(sl1, sl2); }

struct rfl_lemma_prio_fn { unsigned operator()(rfl_lemma const & sl) const { return sl.get_priority(); } };
typedef head_map_prio<rfl_lemma, rfl_lemma_prio_fn> rfl_lemmas;

typedef unsigned rfl_lemmas_token;

/* Register a system level defeq attribute. This method must only be invoked during initialization.
   It returns an internal "token" for retrieving the lemmas */
rfl_lemmas_token register_defeq_simp_attribute(name const & attr_name);

rfl_lemmas get_rfl_lemmas(environment const & env);
rfl_lemmas get_rfl_lemmas(environment const & env, rfl_lemmas_token token);

format pp_rfl_lemmas(rfl_lemmas const & lemmas, formatter const & fmt);

class type_context;

/** \brief (Try to) apply the given rfl_lemma to `e` */
expr rfl_lemma_rewrite(type_context & ctx, expr const & e, rfl_lemma const & sl);

void initialize_rfl_lemmas();
void finalize_rfl_lemmas();
}
