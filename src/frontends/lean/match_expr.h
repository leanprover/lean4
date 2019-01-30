/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/util.h"
namespace lean {
struct parser;
expr parse_match(parser & p, unsigned, expr const *, pos_info const & pos);

void initialize_match_expr();
void finalize_match_expr();
}
