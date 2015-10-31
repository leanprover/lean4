/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/annotation.h"
#include "library/explicit.h"
#include "library/kernel_bindings.h"

namespace lean {
static name * g_explicit_name = nullptr;
static name * g_partial_explicit_name = nullptr;
static name * g_as_atomic_name = nullptr;
static name * g_as_is_name    = nullptr;
static name * g_consume_args_name = nullptr;

expr mk_explicit(expr const & e) { return mk_annotation(*g_explicit_name, e); }
bool is_explicit(expr const & e) { return is_annotation(e, *g_explicit_name); }
bool is_nested_explicit(expr const & e) { return is_nested_annotation(e, *g_explicit_name); }
expr const & get_explicit_arg(expr const & e) { lean_assert(is_explicit(e)); return get_annotation_arg(e); }

expr mk_partial_explicit(expr const & e) { return mk_annotation(*g_partial_explicit_name, e); }
bool is_partial_explicit(expr const & e) { return is_annotation(e, *g_partial_explicit_name); }
bool is_nested_partial_explicit(expr const & e) { return is_nested_annotation(e, *g_partial_explicit_name); }
expr const & get_partial_explicit_arg(expr const & e) { lean_assert(is_partial_explicit(e)); return get_annotation_arg(e); }

expr mk_as_is(expr const & e) { return mk_annotation(*g_as_is_name, e); }
bool is_as_is(expr const & e) { return is_annotation(e, *g_as_is_name); }
expr const & get_as_is_arg(expr const & e) { lean_assert(is_as_is(e)); return get_annotation_arg(e); }

expr mk_as_atomic(expr const & e) { return mk_annotation(*g_as_atomic_name, e); }
bool is_as_atomic(expr const & e) { return is_annotation(e, *g_as_atomic_name); }
expr const & get_as_atomic_arg(expr const & e) { lean_assert(is_as_atomic(e)); return get_annotation_arg(e); }

expr mk_consume_args(expr const & e) { return mk_annotation(*g_consume_args_name, e); }
bool is_consume_args(expr const & e) { return is_annotation(e, *g_consume_args_name); }
expr const & get_consume_args_arg(expr const & e) { lean_assert(is_consume_args(e)); return get_annotation_arg(e); }

void initialize_explicit() {
    g_explicit_name     = new name("@@");
    g_partial_explicit_name     = new name("@");
    g_as_atomic_name    = new name("as_atomic");
    g_as_is_name        = new name("as_is");
    g_consume_args_name = new name("!");

    register_annotation(*g_explicit_name);
    register_annotation(*g_partial_explicit_name);
    register_annotation(*g_as_atomic_name);
    register_annotation(*g_as_is_name);
    register_annotation(*g_consume_args_name);
}

void finalize_explicit() {
    delete g_as_is_name;
    delete g_as_atomic_name;
    delete g_partial_explicit_name;
    delete g_explicit_name;
    delete g_consume_args_name;
}

static int mk_explicit(lua_State * L) { return push_expr(L, mk_explicit(to_expr(L, 1))); }
static int is_explicit(lua_State * L) { return push_boolean(L, is_explicit(to_expr(L, 1))); }
static void check_explicit(lua_State * L, int idx) {
    if (!is_explicit(to_expr(L, idx)))
        throw exception(sstream() << "arg #" << idx << " is not a '@'-expression");
}
static int get_explicit_arg(lua_State * L) {
    check_explicit(L, 1);
    return push_expr(L, get_explicit_arg(to_expr(L, 1)));
}

static int mk_partial_explicit(lua_State * L) { return push_expr(L, mk_partial_explicit(to_expr(L, 1))); }
static int is_partial_explicit(lua_State * L) { return push_boolean(L, is_partial_explicit(to_expr(L, 1))); }
static void check_partial_explicit(lua_State * L, int idx) {
    if (!is_partial_explicit(to_expr(L, idx)))
        throw exception(sstream() << "arg #" << idx << " is not a '@'-expression");
}
static int get_partial_explicit_arg(lua_State * L) {
    check_partial_explicit(L, 1);
    return push_expr(L, get_partial_explicit_arg(to_expr(L, 1)));
}

void open_explicit(lua_State * L) {
    SET_GLOBAL_FUN(mk_explicit,      "mk_explicit");
    SET_GLOBAL_FUN(is_explicit,      "is_explicit");
    SET_GLOBAL_FUN(get_explicit_arg, "get_explicit_arg");

    SET_GLOBAL_FUN(mk_partial_explicit,      "mk_partial_explicit");
    SET_GLOBAL_FUN(is_partial_explicit,      "is_partial_explicit");
    SET_GLOBAL_FUN(get_partial_explicit_arg, "get_partial_explicit_arg");
}
}
