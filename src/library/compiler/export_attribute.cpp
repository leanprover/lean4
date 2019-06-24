/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/util.h"

namespace lean {
object* get_export_name_for_core(object* env, object *n);
optional<name> get_export_name_for(environment const & env, name const & n) {
    return to_optional<name>(get_export_name_for_core(env.to_obj_arg(), n.to_obj_arg()));
}
}
