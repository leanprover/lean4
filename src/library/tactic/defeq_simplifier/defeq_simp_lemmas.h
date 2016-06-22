/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/head_map.h"

namespace lean {

class defeq_simp_lemma {
    name                m_id;
    levels              m_umetas;
    list<expr>          m_emetas;
    list<bool>          m_instances;

    expr                m_lhs;
    expr                m_rhs;
    unsigned            m_priority;
public:
    defeq_simp_lemma() {}
    defeq_simp_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
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

bool operator==(defeq_simp_lemma const & sl1, defeq_simp_lemma const & sl2);
inline bool operator!=(defeq_simp_lemma const & sl1, defeq_simp_lemma const & sl2) { return !operator==(sl1, sl2); }

struct defeq_simp_lemma_prio_fn { unsigned operator()(defeq_simp_lemma const & sl) const { return sl.get_priority(); } };
typedef head_map_prio<defeq_simp_lemma, defeq_simp_lemma_prio_fn> defeq_simp_lemmas;

defeq_simp_lemmas get_defeq_simp_lemmas(environment const & env);
defeq_simp_lemmas get_defeq_simp_lemmas(environment const & env, name const & ns);

format pp_defeq_simp_lemmas(defeq_simp_lemmas const & lemmas, formatter const & fmt, format const & header);

void initialize_defeq_simp_lemmas();
void finalize_defeq_simp_lemmas();
}
