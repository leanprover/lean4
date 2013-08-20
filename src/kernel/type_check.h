/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "expr.h"
#include "context.h"

namespace lean {
class environment;
class type_checker {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    type_checker(environment const & env);
    ~type_checker();

    expr infer_type(expr const & e, context const & ctx = context());
    level infer_universe(expr const & e, context const & ctx = context());
    void check(expr const & e, context const & ctx = context()) { infer_type(e, ctx); }

    void clear();

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
};

expr infer_type(expr const & e, environment const & env, context const & ctx = context());
level infer_universe(expr const & t, environment const & env, context const & ctx = context());
}
