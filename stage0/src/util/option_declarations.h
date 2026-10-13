/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/macros.h"
#include "util/options.h"

namespace lean {
void register_option(name const & n, name const & decl_name, data_value_kind k, char const * default_value, char const * description);
#define register_bool_option(n, v, d) register_option(n, {}, data_value_kind::Bool, LEAN_STR(v), d)
#define register_unsigned_option(n, v, d) register_option(n, {}, data_value_kind::Nat, LEAN_STR(v), d)
#define register_string_option(n, v, d) register_option(n, {}, data_value_kind::String, LEAN_STR(v), d)
}
