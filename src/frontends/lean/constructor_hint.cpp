/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"

namespace lean {
bool has_constructor_hint(environment const & env, name const & d) {
    return has_attribute(env, "constructor", d);
}

void initialize_constructor_hint() {
    register_system_attribute(basic_attribute("constructor",
                                              "instructs elaborator that function application (f ...) should be elaborated as a constructor"));
}
void finalize_constructor_hint() {
}
}
