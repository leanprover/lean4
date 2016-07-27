/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"

namespace lean {
void initialize_old_attributes() {
    register_attribute(prio_attribute("elim", "elimination rule that is eagerly applied by blast grinder"));
    register_attribute(prio_attribute("intro!", "introduction rule that is eagerly applied by blast grinder"));
    register_attribute(basic_attribute("no_pattern", "do not consider terms containing this declaration in the pattern inference procedure"));
    register_attribute(prio_attribute("forward", "forward chaining"));
}
void finalize_old_attributes() {}
}
