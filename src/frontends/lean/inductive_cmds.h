/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "frontends/lean/cmd_table.h"
namespace lean {
void register_inductive_cmds(cmd_table & r);
void initialize_inductive_cmds();
void finalize_inductive_cmds();
}
