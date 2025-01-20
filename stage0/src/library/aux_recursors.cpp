/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/aux_recursors.h"

namespace lean {
extern "C" uint8 lean_is_aux_recursor(object * env, object * n);
extern "C" uint8 lean_is_no_confusion(object * env, object * n);

bool is_aux_recursor(elab_environment const & env, name const & r) {
    return lean_is_aux_recursor(env.to_obj_arg(), r.to_obj_arg());
}

bool is_no_confusion(elab_environment const & env, name const & r) {
    return lean_is_no_confusion(env.to_obj_arg(), r.to_obj_arg());
}
}
