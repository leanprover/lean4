/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <vector>
#include "library/module_mgr.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_manager.h"
namespace lean {
void interactive_report_type(environment const & env, options const & opts, expr const & e, json & j);
void report_completions(environment const & env, options const & opts, pos_info const & pos, bool skip_completions,
                        char const * mod_path, break_at_pos_exception const & e, json & j);
void report_info(environment const & env, options const & opts, io_state const & ios, module_info const & m_mod_info,
                 std::vector<info_manager> const & info_managers, break_at_pos_exception const & e, json & j);

void initialize_interactive();
void finalize_interactive();
}
