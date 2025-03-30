/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/elab_environment.h"
#include "library/reducible.h"

namespace lean {
extern "C" uint8 lean_get_reducibility_status(object * env, object * n);
extern "C" object * lean_set_reducibility_status(object * env, object * n, uint8 s);

elab_environment set_reducible(elab_environment const & env, name const & n, reducible_status s, bool persistent) {
    if (!persistent)
        throw exception("reducibility attributes must be persistent for now, we will relax this restriction in a near future");
    return elab_environment(lean_set_reducibility_status(env.to_obj_arg(), n.to_obj_arg(), static_cast<uint8>(s)));
}

reducible_status get_reducible_status(elab_environment const & env, name const & n) {
    return static_cast<reducible_status>(lean_get_reducibility_status(env.to_obj_arg(), n.to_obj_arg()));
}
}
