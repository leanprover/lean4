/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Rob Lewis
*/
#pragma once
#include "kernel/environment.h"
#include "library/local_context.h"

namespace lean {
class norm_num_context {
    environment   m_env;
    local_context m_ctx;
public:
    norm_num_context(environment const & env, local_context const & ctx):m_env(env), m_ctx(ctx) {}

    bool is_numeral(expr const & e) const;
    pair<expr, expr> mk_norm(expr const & e);
};

inline bool is_numeral(environment const & env, expr const & e) {
    return norm_num_context(env, local_context()).is_numeral(e);
}

inline pair<expr, expr> mk_norm_num(environment const & env, local_context const & ctx, expr const & e) {
    return norm_num_context(env, ctx).mk_norm(e);
}
}
