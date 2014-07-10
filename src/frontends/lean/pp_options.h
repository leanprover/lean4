/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"
namespace lean {
unsigned get_pp_max_depth(options const & opts);
unsigned get_pp_max_steps(options const & opts);
bool     get_pp_notation(options const & opts);
bool     get_pp_implicit(options const & opts);
bool     get_pp_coercion(options const & opts);
bool     get_pp_universes(options const & opts);
bool     get_pp_full_names(options const & opts);
}
