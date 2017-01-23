/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parser.h"
namespace lean {
expr parse_curly_bracket(parser & p, unsigned, expr const * args, pos_info const & pos);
bool is_emptyc_or_emptys(expr const & e);
void initialize_brackets();
void finalize_brackets();
}
