/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"

namespace lean {
static name * g_pattern_attr = nullptr;

static basic_attribute const & get_pattern_attribute() {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_pattern_attr));
}

bool has_pattern_attribute(environment const & env, name const & d) {
    return has_attribute(env, *g_pattern_attr, d);
}

environment set_pattern_attribute(environment const & env, name const & n) {
    return get_pattern_attribute().set(env, get_dummy_ios(), n, LEAN_DEFAULT_PRIORITY, true);
}

void initialize_pattern_attribute() {
    g_pattern_attr = new name({"matchPattern"});
    register_system_attribute(basic_attribute(*g_pattern_attr, "mark that a definition can be used in a pattern"
                                              "(remark: the dependent pattern matching compiler will unfold the definition)"));
}

void finalize_pattern_attribute() {
    delete g_pattern_attr;
}
}
