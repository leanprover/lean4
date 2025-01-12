/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
namespace lean {
struct csimp_cfg {
    /* If `m_inline` == false, then we will not inline `c` even if it is marked with the attribute `[inline]`. */
    bool     m_inline;
    /* We inline "cheap" functions. We say a function is cheap if `get_lcnf_size(val) < m_inline_threshold`,
       and it is not marked as `[noinline]`. */
    unsigned m_inline_threshold;
    /* We only perform float cases_on from cases_on and other expression if the potential code blowup is smaller
       than m_float_cases_threshold. */
    unsigned m_float_cases_threshold;
    /* We inline join-points that are smaller m_inline_threshold. */
    unsigned m_inline_jp_threshold;
public:
    csimp_cfg(options const & opts);
    csimp_cfg();
};

expr csimp_core(elab_environment const & env, local_ctx const & lctx, expr const & e, bool before_erasure, csimp_cfg const & cfg);
inline expr csimp(elab_environment const & env, expr const & e, csimp_cfg const & cfg = csimp_cfg()) {
    return csimp_core(env, local_ctx(), e, true, cfg);
}
inline expr cesimp(elab_environment const & env, expr const & e, csimp_cfg const & cfg = csimp_cfg()) {
    return csimp_core(env, local_ctx(), e, false, cfg);
}
}
