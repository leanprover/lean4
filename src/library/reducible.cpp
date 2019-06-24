/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/environment.h"
#include "library/reducible.h"

namespace lean {
uint8 get_reducibility_status_core(object * env, object * n);
object * set_reducibility_status_core(object * env, object * n, uint8 s);

environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent) {
    if (!persistent)
        throw exception("reducibility attributes must be persistent for now, we will relax this restriction in a near future");
    return environment(set_reducibility_status_core(env.to_obj_arg(), n.to_obj_arg(), static_cast<uint8>(s)));
}

reducible_status get_reducible_status(environment const & env, name const & n) {
    return static_cast<reducible_status>(get_reducibility_status_core(env.to_obj_arg(), n.to_obj_arg()));
}
}
