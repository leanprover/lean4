/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/cmd_table.h"

namespace lean {
void register_migrate_cmd(cmd_table & r);
void initialize_migrate_cmd();
void finalize_migrate_cmd();
}
