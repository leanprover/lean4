/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/elaborator.h"

namespace lean {
MK_THREAD_LOCAL_GET_DEF(type_context_cache_helper, get_tch);

static type_context_cache & get_type_context_cache_for(environment const & env, options const & o) {
    return get_tch().get_cache_for(env, o);
}

elaborator::elaborator(environment const & env, options const & opts, local_level_decls const & lls,
                       metavar_context const & mctx, local_context const & lctx):
    m_env(env), m_opts(opts), m_local_level_decls(lls),
    m_ctx(mctx, lctx, get_type_context_cache_for(env, opts), transparency_mode::Semireducible) {
}

std::tuple<expr, level_param_names> elaborator::operator()(expr const & e) {
    lean_unreachable();
}

std::tuple<expr, level_param_names> elaborate(environment const & env, options const & opts, local_level_decls const & lls,
                                              metavar_context const & mctx, local_context const & lctx, expr const & e) {
    return elaborator(env, opts, lls, mctx, lctx)(e);
}
}
