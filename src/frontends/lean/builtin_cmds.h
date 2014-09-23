/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/cmd_table.h"
namespace lean {
cmd_table get_builtin_cmds();
void initialize_builtin_cmds();
void finalize_builtin_cmds();
}
