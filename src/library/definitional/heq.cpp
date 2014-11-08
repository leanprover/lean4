/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {
bool has_heq_decls(environment const & env) {
    auto d = env.find(name({"heq", "refl"}));
    if (!d)
        return false;
    if (length(d->get_univ_params()) != 1)
        return false;
    expr type = d->get_type();
    for (unsigned i = 0; i < 2; i++) {
        if (!is_pi(type))
            return type;
        type = binding_body(type);
    }
    type = get_app_fn(type);
    if (!is_constant(type))
        return false;
    return const_name(type) == "heq";
}
}
