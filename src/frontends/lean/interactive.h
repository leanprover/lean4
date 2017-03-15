/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "frontends/lean/parser.h"
namespace lean {
format interactive_format_type(environment const & env, options const & opts, expr const & e);
void initialize_interactive();
void finalize_interactive();
}
