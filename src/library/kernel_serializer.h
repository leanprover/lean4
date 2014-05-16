/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/serializer.h"
#include "kernel/definition.h"

namespace lean {
serializer & operator<<(serializer & s, level const & l);
level read_level(deserializer & d);
inline deserializer & operator>>(deserializer & d, level & l) { l = read_level(d); return d; }

serializer & operator<<(serializer & s, levels const & ls);
levels read_levels(deserializer & d);

serializer & operator<<(serializer & s, expr const & e);
expr read_expr(deserializer & d);
inline deserializer & operator>>(deserializer & d, expr & e) { e = read_expr(d); return d; }

serializer & operator<<(serializer & s, definition const & d);
definition read_definition(deserializer & d, unsigned module_idx);

void register_macro_deserializer(std::string const & k, macro_definition_cell::reader rd);
struct register_macro_deserializer_fn {
    register_macro_deserializer_fn(std::string const & k, macro_definition_cell::reader rd) { register_macro_deserializer(k, rd); }
};
}
