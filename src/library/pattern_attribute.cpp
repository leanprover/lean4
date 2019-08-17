/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {
extern "C" uint8 lean_has_match_pattern_attribute(object*, object*);

bool has_pattern_attribute(environment const & env, name const & d) {
    return lean_has_match_pattern_attribute(env.to_obj_arg(), d.to_obj_arg());
}
}
