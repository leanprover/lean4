/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/elab_environment.h"
namespace lean {
extern "C" object* lean_get_implemented_by(object*, object*);

optional<name> get_implemented_by_attribute(elab_environment const & env, name const & n) {
    return to_optional<name>(lean_get_implemented_by(env.to_obj_arg(), n.to_obj_arg()));
}
}
