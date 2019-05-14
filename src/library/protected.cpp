/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/name_set.h"
#include "library/protected.h"
#include "library/module.h"

namespace lean {
object * add_protected_core(object * env, object * n);
uint8 is_protected_core(object * env, object * n);

environment add_protected(environment const & env, name const & n) {
    return environment(add_protected_core(env.get_obj_arg(), n.get_obj_arg()));
}

bool is_protected(environment const & env, name const & n) {
    return is_protected_core(env.get_obj_arg(), n.get_obj_arg());
}

name get_protected_shortest_name(name const & n) {
    if (n.is_atomic() || n.get_prefix().is_atomic()) {
        return n;
    } else {
        name new_prefix = n.get_prefix().replace_prefix(n.get_prefix().get_prefix(), name());
        return n.replace_prefix(n.get_prefix(), new_prefix);
    }
}
}
