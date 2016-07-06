/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"

namespace lean {
void initialize_old_attributes() {
    register_prio_attribute("elim", "elimination rule that is eagerly applied by blast grinder",
                            [](environment const & env, io_state const & ios, name const & d, unsigned prio, name const & ns, bool persistent) {
                                return env;
                            });
    register_prio_attribute("intro!", "introduction rule that is eagerly applied by blast grinder",
                            [](environment const & env, io_state const & ios, name const & d, unsigned prio, name const & ns, bool persistent) {
                                return env;
                            });
    register_no_params_attribute("no_pattern", "do not consider terms containing this declaration in the pattern inference procedure",
                       [](environment const & env, io_state const &, name const & d, name const & ns, bool persistent) {
                           return env;
                       });
    register_prio_attribute("forward", "forward chaining",
                            [](environment const & env, io_state const & ios, name const & d, unsigned prio, name const & ns, bool persistent) {
                                return env;
                            });
}
void finalize_old_attributes() {}
}
