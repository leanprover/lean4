/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#include "runtime/object_ref.h"
#include "library/elab_environment.h"

namespace lean {
extern "C" object* lean_get_init_fn_name_for(object* env, object* fn);

optional<name> get_init_fn_name_for(elab_environment const & env, name const & n) {
    return to_optional<name>(lean_get_init_fn_name_for(env.to_obj_arg(), n.to_obj_arg()));
}
}
