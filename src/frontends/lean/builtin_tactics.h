/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parse_table.h"

namespace lean {
void init_nud_tactic_table(parse_table & r);
void initialize_builtin_tactics();
void finalize_builtin_tactics();
}
