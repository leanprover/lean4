/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/cmd_table.h"
#include "library/message_builder.h"
namespace lean {
bool print_id_info(parser & p, message_builder & out, name const & id, bool show_value, pos_info const & pos);
bool print_token_info(parser const & p, message_builder & out, name const & tk);

cmd_table get_builtin_cmds();
/* \brief Replay export declarations in the top-level of imported files */
environment replay_export_decls_core(environment env, io_state const & ios);

void initialize_builtin_cmds();
void finalize_builtin_cmds();
}
