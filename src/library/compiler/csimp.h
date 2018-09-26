/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
struct csimp_cfg {
    bool     m_inline;
    unsigned m_inline_threshold;
    bool     m_float_cases_app;
    bool     m_float_cases;
    unsigned m_float_cases_jp_threshold;
    unsigned m_float_cases_jp_branch_threshold;
    unsigned m_inline_jp_threshold;
public:
    csimp_cfg();
};

expr csimp(environment const & env, local_ctx const & lctx, expr const & e, csimp_cfg const & cfg = csimp_cfg());
}
