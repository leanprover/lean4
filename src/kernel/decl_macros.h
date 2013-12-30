/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
/**
   \brief Helper macro for defining constants such as bool_type, int_type, int_add, etc.
*/
#define MK_BUILTIN(Name, ClassName)                                     \
expr mk_##Name() {                                                      \
    static LEAN_THREAD_LOCAL expr r = mk_value(*(new ClassName()));     \
    return r;                                                           \
}

/**
   \brief Helper macro for generating "defined" constants.
*/
#define MK_CONSTANT(Name, NameObj)                                      \
static name Name ## _name = NameObj;                                    \
expr mk_##Name() {                                                      \
    static LEAN_THREAD_LOCAL expr r = mk_constant(Name ## _name);       \
    return r ;                                                          \
}                                                                       \
bool is_ ## Name(expr const & e) {                                      \
    return is_constant(e) && const_name(e) == Name ## _name;            \
}

#define MK_IS_BUILTIN(Name, Builtin)                                    \
bool Name(expr const & e) {                                             \
    expr const & v = Builtin;                                           \
    return e == v || (is_constant(e) && const_name(e) == to_value(v).get_name()); \
}
