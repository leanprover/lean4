/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/expr.h"

namespace lean {
class ro_environment;
class options;
/** \brief Functional object for normalizing expressions */
class normalizer {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    normalizer(ro_environment const & env);
    normalizer(ro_environment const & env, unsigned max_depth);
    normalizer(ro_environment const & env, options const & opts);
    ~normalizer();

    expr operator()(expr const & e);
    void clear();
};

/** \brief Normalize \c e using the environment \c env and context \c ctx */
expr normalize(expr const & e, ro_environment const & env);
}
