/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/app_builder.h"
#include "library/fun_info_manager.h"

namespace lean {
class congr_lemma_manager {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    congr_lemma_manager(app_builder & b, fun_info_manager & fm);
    ~congr_lemma_manager();

    enum class congr_arg_kind { Fixed, Eq, Cast };

    typedef pair<expr, list<congr_arg_kind>> result;
    optional<result> mk_congr_simp(expr const & fn);
};
}
