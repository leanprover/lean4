/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/pos_info_provider.h"
#include "library/local_context.h"
#include "library/type_context.h"
#include "frontends/lean/elaborator_context.h"

namespace lean {
class elaborator {
    environment    m_env;
    options        m_opts;
    type_context   m_ctx;

    expr visit(expr const & e, optional<expr> const & expected_type);

public:
    elaborator(environment const & env, options const & opts, local_level_decls const & lls,
               metavar_context const & mctx, local_context const & lctx);

    std::tuple<expr, level_param_names> elaborate(expr const & e, optional<expr> const & expected_type);
};

std::tuple<expr, level_param_names> elaborate(elaborator_context const & ectx, local_context const & lctx, expr const & e);
}
