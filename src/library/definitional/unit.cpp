/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {
bool has_unit_decls(environment const & env) {
    auto d = env.find(name({"unit", "star"}));
    if (!d)
        return false;
    if (length(d->get_univ_params()) != 1)
        return false;
    expr const & type = d->get_type();
    if (!is_constant(type))
        return false;
    return const_name(type) == "unit";
}
}
