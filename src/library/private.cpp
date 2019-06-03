/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "runtime/sstream.h"
#include "runtime/hash.h"
#include "library/private.h"
#include "library/module.h"

namespace lean {
object* mk_private_prefix_core(object *);
object* mk_private_name_core(object*, object*);
object* is_private_name_core(object*);
object* private_to_user_name_core(object*);
object* private_prefix_core(object*);

pair<environment, name> mk_private_prefix(environment const & env) {
    pair_ref<environment, name> r(mk_private_prefix_core(env.to_obj_arg()));
    return mk_pair(r.fst(), r.snd());
}

pair<environment, name> mk_private_name(environment const & env, name const & n) {
    pair_ref<environment, name> r(mk_private_name_core(env.to_obj_arg(), n.to_obj_arg()));
    return mk_pair(r.fst(), r.snd());
}

optional<name> private_to_user_name(name const & n) {
    return to_optional<name>(private_to_user_name_core(n.to_obj_arg()));
}

bool is_private(name const & n) {
    return is_private_name_core(n.to_obj_arg());
}

optional<name> get_private_prefix(name const & n) {
    return to_optional<name>(private_prefix_core(n.to_obj_arg()));
}

void initialize_private() {
}

void finalize_private() {
}
}
