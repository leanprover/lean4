/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {
uint8 has_match_pattern_attribute_core(object*, object*);

bool has_pattern_attribute(environment const & env, name const & d) {
    return has_match_pattern_attribute_core(env.to_obj_arg(), d.to_obj_arg());
}
}
