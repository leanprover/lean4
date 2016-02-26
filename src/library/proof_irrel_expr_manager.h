/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <vector>
#include "kernel/expr.h"
#include "library/type_context.h"
#include "library/fun_info_manager.h"

namespace lean {

/** \brief Proof-irrelevant expression manager, to allow comparing expressions while ignoring proofs. */

class proof_irrel_expr_manager {
    /* The [fun_info_manager] cannot handle [Var]s since it needs to infer types, and we do not
       want to instantiate eagerly for performance reasons. Therefore we track the context ourselves,
       and only instantiate on the expressions we pass to the [fun_info_manager], which we
       expect to be very small in general. */
    std::vector<expr>     m_locals;
    type_context        & m_tctx;
    fun_info_manager    & m_fun_info_manager;
public:
    proof_irrel_expr_manager(fun_info_manager & f_info_manager):
        m_tctx(f_info_manager.ctx()), m_fun_info_manager(f_info_manager) {}
    unsigned hash(expr const & e);
    bool is_equal(expr const & a, expr const & b);
};

}
