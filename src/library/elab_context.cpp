/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/elab_context.h"

namespace lean {
elab_context::elab_context(environment const & env, metavar_context const & mctx, name_generator const & ngen, abstract_context_cache * cache):
    m_env(env),
    m_mctx(mctx),
    m_ngen(ngen),
    m_cache(cache) {
}

elab_context::elab_context(environment const & env, metavar_context const & mctx, name_generator const & ngen, options const & opts):
    m_env(env),
    m_mctx(mctx),
    m_ngen(ngen),
    m_dummy_cache(opts),
    m_cache(&m_dummy_cache) {
}
}
