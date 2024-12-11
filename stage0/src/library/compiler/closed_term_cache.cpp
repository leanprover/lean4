/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/util.h"
#include "library/elab_environment.h"

namespace lean {
extern "C" object * lean_cache_closed_term_name(object * env, object * e, object * n);
extern "C" object * lean_get_closed_term_name(object * env, object * e);

optional<name> get_closed_term_name(elab_environment const & env, expr const & e) {
    return to_optional<name>(lean_get_closed_term_name(env.to_obj_arg(), e.to_obj_arg()));
}

elab_environment cache_closed_term_name(elab_environment const & env, expr const & e, name const & n) {
    return elab_environment(lean_cache_closed_term_name(env.to_obj_arg(), e.to_obj_arg(), n.to_obj_arg()));
}
}
