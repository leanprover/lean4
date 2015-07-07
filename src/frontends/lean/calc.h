/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/cmd_table.h"
namespace lean {
class parser;
expr parse_calc(parser & p);
bool is_calc_annotation(expr const & e);
void initialize_calc();
void finalize_calc();
}
