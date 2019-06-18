/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#include "util/object_ref.h"
#include "kernel/environment.h"

namespace lean {
object* get_init_fn_name_for_core(object* env, object* fn);

optional<name> get_init_fn_name_for(environment const & env, name const & n) {
    return to_optional<name>(get_init_fn_name_for_core(env.to_obj_arg(), n.to_obj_arg()));
}
}
