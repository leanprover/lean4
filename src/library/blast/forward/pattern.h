/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_multi_map.h"
#include "kernel/environment.h"
#include "library/tmp_type_context.h"

#ifndef LEAN_HI_LEMMA_DEFAULT_PRIORITY
#define LEAN_HI_LEMMA_DEFAULT_PRIORITY 1000
#endif

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
environment add_no_pattern(environment const & env, name const & n, bool persistent);
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
    expr                 m_prop;
    expr                 m_proof;
};

inline bool operator==(hi_lemma const & l1, hi_lemma const & l2) { return l1.m_prop == l2.m_prop; }
inline bool operator!=(hi_lemma const & l1, hi_lemma const & l2) { return l1.m_prop != l2.m_prop; }

/** \brief Mapping c -> S, where c is a constant name and S is a set of hi_lemmas that contain
    a pattern where the head symbol is c. */
typedef rb_multi_map<name, hi_lemma, name_quick_cmp> hi_lemmas;

/** \brief Add the given theorem as a heuristic instantiation lemma in the current environment. */
environment add_hi_lemma(environment const & env, options const & o, name const & c, unsigned priority, bool persistent);

/** \brief Return the heuristic instantiation lemma data associated with constant \c c */
hi_lemma const * get_hi_lemma(environment const & env, name const & c);

/** \brief Retrieve the active set of heuristic instantiation lemmas. */
hi_lemmas get_hi_lemma_index(environment const & env);

hi_lemma mk_hi_lemma(tmp_type_context & ctx, expr const & H, unsigned max_steps);

unsigned get_pattern_max_steps(options const & o);

namespace blast {
/** \brief Create a (local) heuristic instantiation lemma for \c H.
    The maximum number of steps is extracted from the blast config object. */
hi_lemma mk_hi_lemma(tmp_type_context & ctx, expr const & H);
}

void initialize_pattern();
void finalize_pattern();
}
