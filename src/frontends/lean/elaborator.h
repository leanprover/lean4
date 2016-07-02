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
    environment       m_env;
    options           m_opts;
    local_level_decls m_local_level_decls;
    type_context      m_ctx;

    /* if m_no_info is true, we do not collect information when true,
       we set is to true whenever we find no_info annotation. */
    bool                 m_no_info{true};

    expr visit(expr const & e, optional<expr> const & expected_type);

public:
    elaborator(environment const & env, options const & opts, local_level_decls const & lls,
               metavar_context const & mctx, local_context const & lctx);

    std::tuple<expr, level_param_names> operator()(expr const & e);
};

std::tuple<expr, level_param_names> elaborate(environment const & env, options const & opts, local_level_decls const & lls,
                                              metavar_context const & mctx, local_context const & lctx, expr const & e);
}
