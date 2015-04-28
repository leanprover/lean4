/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parse_table.h"
namespace lean {
parse_table get_builtin_tactic_nud_table();
parse_table get_builtin_tactic_led_table();
void initialize_builtin_tactics();
void finalize_builtin_tactics();
}
