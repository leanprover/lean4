/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include "library/attribute_manager.h"

namespace lean {
bool has_extern_attribute(environment const & env, name const & d) {
    return has_attribute(env, "extern", d);
}

std::string library_name(environment const & env, name const & d) {
    auto attr = static_cast<key_value_attribute const &>(get_attribute(env, "extern"));
    auto data = attr.get(env, d);
    return data->m_library;
}

std::string symbol_name(environment const & env, name const & d) {
    auto attr = static_cast<key_value_attribute const &>(get_attribute(env, "extern"));
    auto data = attr.get(env, d);
    return data->m_symbol;
}

void initialize_extern_attribute() {
    register_system_attribute(key_value_attribute("extern", "mark a constant as external to Lean"));
}

void finalize_extern_attribute() {
}
}
