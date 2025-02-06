/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/util.h"
#include "library/elab_environment.h"

namespace lean {
extern "C" object* lean_get_export_name_for(object* env, object *n);
optional<name> get_export_name_for(elab_environment const & env, name const & n) {
    return to_optional<name>(lean_get_export_name_for(env.to_obj_arg(), n.to_obj_arg()));
}
}
