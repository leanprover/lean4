/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parse_table.h"
namespace lean {
parse_table get_builtin_nud_table();
parse_table get_builtin_led_table();
void initialize_builtin_exprs();
void finalize_builtin_exprs();
}
