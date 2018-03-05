/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_multi_map.h"
#include "kernel/environment.h"
#include "library/expr_lt.h"
#include "library/type_context.h"
#include "library/io_state_stream.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"

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
environment add_no_inst_pattern_attribute(environment const & env, name const & n);
/** \brief Return true if constant \c n is marked as [no_pattern] in the given environment. */
bool has_no_inst_pattern_attribute(environment const & env, name const & n);
/** \brief Return the set of constants marked as no-patterns */
name_set get_no_inst_patterns(environment const & env);

typedef list<expr> multi_pattern;

/** Heuristic instantiation lemma */
struct hinst_lemma {
    name                 m_id;
    unsigned             m_num_uvars{0};
    unsigned             m_num_mvars{0};
    list<multi_pattern>  m_multi_patterns;
    list<bool>           m_is_inst_implicit;
    list<expr>           m_mvars;
    expr                 m_prop;
    expr                 m_proof;
    /* term that was used to generate hinst_lemma, it is only used for tracing and profiling */
    expr                 m_expr;
};

inline int multi_pattern_cmp(multi_pattern const & m1, multi_pattern const & m2) {
    return cmp<expr>(m1, m2, expr_quick_cmp());
}

struct hinst_lemma_cmp {
    int operator()(hinst_lemma const & l1, hinst_lemma const & l2) const {
        int r = expr_quick_cmp()(l1.m_prop, l2.m_prop);
        if (r != 0) return r;
        return cmp(l1.m_multi_patterns, l2.m_multi_patterns, multi_pattern_cmp);
    }
};

typedef rb_tree<hinst_lemma, hinst_lemma_cmp> hinst_lemmas;

/** \brief Try to compute multipatterns for declaration \c c using the current environment configuration. */
list<multi_pattern> mk_multipatterns(environment const & env, io_state const & ios, name const & c);

/** \brief Create a (local) heuristic instantiation lemma for \c H.
    The maximum number of steps is extracted from the blast config object.

    \c md_norm is the transparency_mode used for normalizing the type of the lemma.
    The idea is to unfold the lemmas using the given transparency mode. */
hinst_lemma mk_hinst_lemma(type_context_old & ctx, transparency_mode md_norm, expr const & H, bool simp = false);
hinst_lemma mk_hinst_lemma(type_context_old & ctx, transparency_mode md_norm, name const & n, bool simp = false);

format pp_hinst_lemma(formatter const & fmt, hinst_lemma const & h);

inline io_state_stream const & operator<<(io_state_stream const & out, hinst_lemma const & e) {
    out << mk_pair(pp_hinst_lemma(out.get_formatter(), e), out.get_options());
    return out;
}

bool is_hinst_lemma(vm_obj const & o);
hinst_lemma const & to_hinst_lemma(vm_obj const & o);
vm_obj to_obj(hinst_lemma const & s);

bool is_hinst_lemmas(vm_obj const & o);
hinst_lemmas const & to_hinst_lemmas(vm_obj const & o);
vm_obj to_obj(hinst_lemmas const & s);

void initialize_hinst_lemmas();
void finalize_hinst_lemmas();
}
