/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/thread.h"
#include "kernel/find_fn.h"
#include "library/placeholder.h"
#include "library/kernel_bindings.h"

namespace lean {
static name g_placeholder_name = name(name::mk_internal_unique_name(), "_");
MK_THREAD_LOCAL_GET(unsigned, get_placeholder_id, 0)
static unsigned next_placeholder_id() {
    unsigned & c = get_placeholder_id();
    unsigned r = c;
    c++;
    return r;
}
level mk_level_placeholder() { return mk_global_univ(name(g_placeholder_name, next_placeholder_id())); }
expr mk_expr_placeholder() { return mk_constant(name(g_placeholder_name, next_placeholder_id())); }
static bool is_placeholder(name const & n) { return !n.is_atomic() && n.get_prefix() == g_placeholder_name; }
bool is_placeholder(level const & e) { return is_global(e) && is_placeholder(global_id(e)); }
bool is_placeholder(expr const & e) { return is_constant(e) && is_placeholder(const_name(e)); }

bool has_placeholder(level const & l) {
    bool r = false;
    for_each(l, [&](level const & e) {
            if (is_placeholder(e))
                r = true;
            return !r;
        });
    return r;
}

bool has_placeholder(expr const & e) {
    return (bool) find(e, [](expr const & e, unsigned) { // NOLINT
            if (is_placeholder(e))
                return true;
            else if (is_sort(e))
                return has_placeholder(sort_level(e));
            else if (is_constant(e))
                return std::any_of(const_levels(e).begin(), const_levels(e).end(), [](level const & l) { return has_placeholder(l); });
            else
                return false;
        });
}

static int mk_level_placeholder(lua_State * L) { return push_level(L, mk_level_placeholder()); }
static int mk_expr_placeholder(lua_State * L) { return push_expr(L, mk_expr_placeholder()); }
static int is_placeholder(lua_State * L) {
    if (is_expr(L, 1))
        return push_boolean(L, is_placeholder(to_expr(L, 1)));
    else
        return push_boolean(L, is_placeholder(to_level(L, 1)));
}
static int has_placeholder(lua_State * L) {
    if (is_expr(L, 1))
        return push_boolean(L, has_placeholder(to_expr(L, 1)));
    else
        return push_boolean(L, has_placeholder(to_level(L, 1)));
}

void open_placeholder(lua_State * L) {
    SET_GLOBAL_FUN(mk_level_placeholder, "mk_level_placeholder");
    SET_GLOBAL_FUN(mk_expr_placeholder,  "mk_expr_placeholder");
    SET_GLOBAL_FUN(is_placeholder,       "is_placeholder");
    SET_GLOBAL_FUN(has_placeholder,      "has_placeholder");
}
}
