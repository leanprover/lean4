/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {
expr bool_type();
bool is_bool_type(expr const & e);

expr bool_value(bool v);
bool is_bool_value(expr const & e);
bool to_bool(expr const & e);
bool is_true(expr const & e);
bool is_false(expr const & e);

class environment;
void add_basic_theory(environment & env);

/**
   \brief Helper macro for defining constants such as bool_type, int_type, int_add, etc.
*/
#define MK_BUILTIN(Name, ClassName)                                     \
expr Name() {                                                           \
    static thread_local expr r;                                         \
    if (!r)                                                             \
        r = to_expr(*(new ClassName()));                                \
    return r;                                                           \
}                                                                       \
bool is_##Name(expr const & e) {                                        \
    return is_value(e) && to_value(e).kind() == ClassName::g_kind;      \
}

/**
   \brief Helper macro for generating "defined" constants.
*/
#define MK_CONSTANT(Name, NameObj)                                      \
static name Name ## _name_obj = NameObj;                                \
expr Name() {                                                           \
    static thread_local expr r;                                         \
    if (!r)                                                             \
        r = constant(Name ## _name_obj);                                \
    return r;                                                           \
}                                                                       \
bool is_##Name(expr const & e) {                                        \
    return is_constant(e) && const_name(e) == Name ## _name_obj;        \
}

}
