/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/serializer.h"
#include "kernel/declaration.h"
#include "kernel/inductive/inductive.h"

namespace lean {
serializer & operator<<(serializer & s, level const & l);
level read_level(deserializer & d);
inline deserializer & operator>>(deserializer & d, level & l) { l = read_level(d); return d; }

serializer & operator<<(serializer & s, levels const & ls);
levels read_levels(deserializer & d);

serializer & operator<<(serializer & s, level_param_names const & ps);
level_param_names read_level_params(deserializer & d);
inline deserializer & operator>>(deserializer & d, level_param_names & ps) { ps = read_level_params(d); return d; }

serializer & operator<<(serializer & s, expr const & e);
expr read_expr(deserializer & d);
inline deserializer & operator>>(deserializer & d, expr & e) { e = read_expr(d); return d; }

serializer & operator<<(serializer & s, declaration const & d);
declaration read_declaration(deserializer & d);

serializer & operator<<(serializer & s, inductive::certified_inductive_decl const & d);
inductive::certified_inductive_decl read_certified_inductive_decl(deserializer & d);

void register_macro_deserializer(std::string const & k, macro_definition_cell::reader rd);
void initialize_kernel_serializer();
void finalize_kernel_serializer();
}
