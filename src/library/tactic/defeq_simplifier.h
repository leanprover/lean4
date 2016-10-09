/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "library/type_context.h"
#include "library/simp_lemmas.h"

namespace lean {
class defeq_simplifier_exception : public exception {
public:
    defeq_simplifier_exception(char const * msg):exception(msg) {}
    defeq_simplifier_exception(sstream const & strm):exception(strm) {}
    virtual throwable * clone() const override { return new defeq_simplifier_exception(m_msg.c_str()); }
    virtual void rethrow() const override { throw *this; }
};

expr defeq_simplify(type_context & ctx, simp_lemmas const & simp_lemmas, expr const & e);
expr defeq_simplify(type_context & ctx, expr const & e);
void initialize_defeq_simplifier();
void finalize_defeq_simplifier();
}
