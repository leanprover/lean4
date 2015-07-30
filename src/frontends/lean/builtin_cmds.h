/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/cmd_table.h"
namespace lean {
bool print_id_info(parser const & p, name const & id, bool show_value, pos_info const & pos);
bool print_token_info(parser const & p, name const & tk);

cmd_table get_builtin_cmds();
void initialize_builtin_cmds();
void finalize_builtin_cmds();
}
