/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"

namespace lean {
optional<name> get_init_fn_name_for(elab_environment const & env, name const & n);
inline bool has_init_attribute(elab_environment const & env, name const & n) {
    return static_cast<bool>(get_init_fn_name_for(env, n));
}
}
