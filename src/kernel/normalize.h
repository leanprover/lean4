/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "expr.h"
#include "environment.h"
#include "context.h"

namespace lean {
class environment;
/** \brief Functional object for normalizing expressions */
class normalizer {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    normalizer(environment const & env);
    ~normalizer();

    expr operator()(expr const & e, context const & ctx = context());
    bool is_convertible(expr const & t1, expr const & t2, context const & ctx = context());

    void clear();

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
};
/** \brief Normalize \c e using the environment \c env and context \c ctx */
expr normalize(expr const & e, environment const & env, context const & ctx = context());
bool is_convertible(expr const & t1, expr const & t2, environment const & env, context const & ctx = context());
}
