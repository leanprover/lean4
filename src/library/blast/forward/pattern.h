/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_multi_map.h"
#include "kernel/environment.h"
#include "library/expr_lt.h"
#include "library/tmp_type_context.h"

namespace lean {
/** \brief Annotate \c e as a pattern hint */
expr mk_pattern_hint(expr const & e);
/** \brief Return true iff \c e is an annotated pattern */
bool is_pattern_hint(expr const & e);
/** \brief Return the actual pattern */
expr const & get_pattern_hint_arg(expr const & e);
/** \brief Return true iff \c e contains pattern hints */
bool has_pattern_hints(expr const & e);

/** \brief Hint for the pattern inference procedure.
    It should not consider/infer patterns containing the constant \c n. */
environment add_no_pattern(environment const & env, name const & n, name const & ns, bool persistent);
/** \brief Return true if constant \c n is marked as [no_pattern] in the given environment. */
bool is_no_pattern(environment const & env, name const & n);
/** \brief Return the set of constants marked as no-patterns */
name_set const & get_no_patterns(environment const & env);

typedef list<expr> multi_pattern;

/** Heuristic instantiation lemma */
struct hi_lemma {
    unsigned             m_num_uvars;
    unsigned             m_num_mvars;
    unsigned             m_priority;
    list<multi_pattern>  m_multi_patterns;
    list<bool>           m_is_inst_implicit;
    list<expr>           m_mvars;
    expr                 m_prop;
    expr                 m_proof;
};

inline bool operator==(hi_lemma const & l1, hi_lemma const & l2) { return l1.m_prop == l2.m_prop; }
inline bool operator!=(hi_lemma const & l1, hi_lemma const & l2) { return l1.m_prop != l2.m_prop; }
struct hi_lemma_cmp {
    int operator()(hi_lemma const & l1, hi_lemma const & l2) const { return expr_quick_cmp()(l1.m_prop, l2.m_prop); }
};

/** \brief Try to compute multipatterns for declaration \c c using the current environment configuration. */
list<multi_pattern> mk_multipatterns(environment const & env, io_state const & ios, name const & c);

namespace blast {
/** \brief Create a (local) heuristic instantiation lemma for \c H.
    The maximum number of steps is extracted from the blast config object. */
hi_lemma mk_hi_lemma(expr const & H);
hi_lemma mk_hi_lemma(name const & n, unsigned prio);
}

void initialize_pattern();
void finalize_pattern();
}
