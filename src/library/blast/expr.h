/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/declaration.h"

namespace lean {
namespace blast {
level mk_uref(unsigned idx);

bool is_uref(level const & l);
unsigned uref_index(level const & l);

// mk_href and mk_mref are helper functions for creating hypotheses and meta-variables used in the blast tactic.
// Remark: the local constants and metavariables manipulated by the blast tactic do **not** store their types.
expr mk_href(unsigned idx);
expr mk_mref(unsigned idx);

bool is_href(expr const & e);
unsigned href_index(expr const & e);
bool is_mref(expr const & e);
unsigned mref_index(expr const & e);
/** \brief Return true iff \c e contain href's */
bool has_href(expr const & e);
/** \brief Return true iff \c e contain mref's */
bool has_mref(expr const & e);

inline bool is_local_non_href(expr const & e) { return is_local(e) && !is_href(e); }

/** \brief Return the a fresh index for uref/mref/href.
    \remark It is implemented using thread local storage. */
unsigned mk_uref_idx();
unsigned mk_mref_idx();
unsigned mk_href_idx();
/** \brief Reset thread local counters */
void init_uref_mref_href_idxs();

inline level mk_fresh_uref() { return mk_uref(mk_uref_idx()); }

void initialize_expr();
void finalize_expr();
}
}
