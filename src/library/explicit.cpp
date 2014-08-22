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
name const & get_explicit_name() {
    static name g_explicit_name("@");
    static register_annotation_fn g_explicit_annotation(g_explicit_name);
    return g_explicit_name;
}

name const & get_implicit_name() {
    static name g_implicit_name("@^-1");
    static register_annotation_fn g_implicit_annotation(g_implicit_name);
    return g_implicit_name;
}

name const & get_as_is_name() {
    static name g_as_is_name("as_is");
    static register_annotation_fn g_as_is_annotation(g_as_is_name);
    return g_as_is_name;
}
static name g_explicit_name = get_explicit_name(); // force '@' annotation to be registered
static name g_implicit_name = get_implicit_name(); // force '@^-1' annotation to be registered
static name g_as_is_name    = get_as_is_name();    // force 'as_is' annotation to be registered

expr mk_explicit(expr const & e) { return mk_annotation(get_explicit_name(), e); }
bool is_explicit(expr const & e) { return is_annotation(e, get_explicit_name()); }
expr mk_as_is(expr const & e) { return mk_annotation(get_as_is_name(), e); }
bool is_as_is(expr const & e) { return is_annotation(e, get_as_is_name()); }
expr mk_implicit(expr const & e) { return mk_annotation(get_implicit_name(), e); }
bool is_implicit(expr const & e) { return is_annotation(e, get_implicit_name()); }
expr const & get_explicit_arg(expr const & e) { lean_assert(is_explicit(e)); return get_annotation_arg(e); }
expr const & get_as_is_arg(expr const & e) { lean_assert(is_as_is(e)); return get_annotation_arg(e); }
expr const & get_implicit_arg(expr const & e) { lean_assert(is_implicit(e)); return get_annotation_arg(e); }

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

void open_explicit(lua_State * L) {
    SET_GLOBAL_FUN(mk_explicit,      "mk_explicit");
    SET_GLOBAL_FUN(is_explicit,      "is_explicit");
    SET_GLOBAL_FUN(get_explicit_arg, "get_explicit_arg");
}
}
