/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <vector>
#include "kernel/expr.h"
#include "library/type_context.h"
#include "library/congr_lemma_manager.h"

namespace lean {

/** \brief Abstract expression manager, to allow comparing expressions while ignoring subsingletons. */

class abstract_expr_manager {
    /* The [congr_lemma_manager] cannot handle [Var]s since it needs to infer types, and we do not
       want to instantiate eagerly for performance reasons. Therefore we track the context ourselves,
       and only instantiate on the expressions we pass to the [congr_lemma_manager], which we
       expect to be very small in general. */
    std::vector<expr>     m_locals;
    type_context        & m_tctx;
    congr_lemma_manager & m_congr_lemma_manager;
public:
    abstract_expr_manager(congr_lemma_manager & c_lemma_manager):
        m_tctx(c_lemma_manager.ctx()), m_congr_lemma_manager(c_lemma_manager) {}
    unsigned hash(expr const & e);
    bool is_equal(expr const & a, expr const & b);
};

}
