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
// API for creating maximally shared terms used by the blast tactic.
// The API assumes there is a single blast tactic using theses terms.
// The expression hash-consing tables are thread local and implemented
// in the kernel

// Remark: All procedures assume the children levels and expressions are maximally shared.
// That is, it assumes they have been created using the APIs provided by this module.

// Auxiliary object for resetting the the thread local hash-consing tables.
// It also uses an assertion to make sure it is not being used in a recursion.
class scope_hash_consing : public scoped_expr_caching {
public:
    scope_hash_consing();
    ~scope_hash_consing();
};

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

inline bool is_local_non_href(expr const & e) {
    return is_local(e) && !is_href(e);
}

void initialize_expr();
void finalize_expr();
}
}
