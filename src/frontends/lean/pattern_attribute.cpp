/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"

namespace lean {
bool has_pattern_attribute(environment const & env, name const & d) {
    return has_attribute(env, "pattern", d);
}

void initialize_pattern_attribute() {
    register_system_attribute(basic_attribute("pattern", "mark that a definition can be used in a pattern"
            "(remark: the dependent pattern matching compiler will unfold the definition)"));
}

void finalize_pattern_attribute() {
}
}
