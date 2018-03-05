/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/type_context.h"

namespace lean {
/** \brief Helper class for making sure we have a cache that is compatible
    with a given environment and transparency mode. */
template<typename Cache>
class cache_compatibility_helper {
    std::unique_ptr<Cache> m_cache_ptr[LEAN_NUM_TRANSPARENCY_MODES];
public:
    Cache & get_cache_for(environment const & env, transparency_mode m) {
        unsigned midx = static_cast<unsigned>(m);
        if (!m_cache_ptr[midx] || !is_eqp(env, m_cache_ptr[midx]->env())) {
            m_cache_ptr[midx].reset(new Cache(env));
        }
        return *m_cache_ptr[midx].get();
    }

    Cache & get_cache_for(type_context_old const & ctx) {
        return get_cache_for(ctx.env(), ctx.mode());
    }

    void clear() {
        for (unsigned i = 0; i < 4; i++) m_cache_ptr[i].reset();
    }
};
}
