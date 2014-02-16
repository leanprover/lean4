/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include <functional>
#include "util/buffer.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"

namespace lean {
/**
    \brief Expression visitor.

    The argument \c F must be a lambda (function object) containing the method

    <code>
    void operator()(expr const & e, unsigned offset)
    </code>

    The \c offset is the number of binders under which \c e occurs.
*/
class for_each_fn {
    std::unique_ptr<expr_cell_offset_set>       m_visited;
    std::function<bool(expr const &, unsigned)> m_f;
    void apply(expr const & e, unsigned offset);
public:
    template<typename F> for_each_fn(F && f):m_f(f) {}
    template<typename F> for_each_fn(F const & f):m_f(f) {}
    void operator()(expr const & e) { apply(e, 0); }
};

template<typename F> void for_each(expr const & e, F && f) {
    return for_each_fn(f)(e);
}
}
