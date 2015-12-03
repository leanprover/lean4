/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "library/fun_info_manager.h"
#include "library/congr_lemma_manager.h"

namespace lean {

/** \brief Abstract expression manager, to allow comparing expressions while ignoring subsingletons. */

class abstract_expr_manager {
    congr_lemma_manager & m_congr_lemma_manager;
public:
    abstract_expr_manager(congr_lemma_manager & c_lemma_manager): m_congr_lemma_manager(c_lemma_manager) {}
    unsigned hash(expr const & e);
    bool is_equal(expr const & a, expr const & b);
};

}
