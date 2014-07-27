/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/list.h"
#include "kernel/environment.h"
#include "kernel/metavar.h"
#include "library/io_state.h"
#include "frontends/lean/local_decls.h"

namespace lean {
std::tuple<expr, level_param_names> elaborate(environment const & env, local_decls<level> const & lls, list<expr> const & ctx,
                                              io_state const & ios, expr const & e, bool relax_main_opaque,
                                              pos_info_provider * pp = nullptr, bool check_unassigned = true, bool ensure_type = false);
std::tuple<expr, expr, level_param_names> elaborate(environment const & env, local_decls<level> const & lls,
                                                    io_state const & ios, name const & n, expr const & t, expr const & v,
                                                    bool is_opaque, pos_info_provider * pp = nullptr);
}
