/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/expr.h"

namespace lean {
expr mk_unit(level const & l);
expr mk_unit_mk(level const & l);

expr mk_bool_true();
expr mk_bool_false();

LEAN_EXPORT std::string const & get_short_version_string();

void initialize_library_util();
void finalize_library_util();
}
