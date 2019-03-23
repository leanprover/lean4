/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
bool is_io_unit_init_fn(environment const & env, name const & n);
optional<name> get_init_fn_name_for(environment const & env, name const & n);
inline bool has_init_attribute(environment const & env, name const & n) {
    return static_cast<bool>(get_init_fn_name_for(env, n));
}
void initialize_init_attribute();
void finalize_init_attribute();
}
