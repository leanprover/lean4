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
static name * g_implicit_placeholder_name = nullptr;
static name * g_placeholder_name          = nullptr;
static name * g_strict_placeholder_name   = nullptr;
static name * g_explicit_placeholder_name = nullptr;

void initialize_placeholder() {
    g_implicit_placeholder_name = new name(name::mk_internal_unique_name(), "_");
    g_placeholder_name          = g_implicit_placeholder_name;
    g_strict_placeholder_name   = new name(name::mk_internal_unique_name(), "_");
    g_explicit_placeholder_name = new name(name::mk_internal_unique_name(), "_");
}

void finalize_placeholder() {
    delete g_implicit_placeholder_name;
    delete g_strict_placeholder_name;
    delete g_explicit_placeholder_name;
}

LEAN_THREAD_VALUE(unsigned, g_placeholder_id, 0);
static unsigned next_placeholder_id() {
    unsigned r = g_placeholder_id;
    g_placeholder_id++;
    return r;
}
level mk_level_placeholder() { return mk_global_univ(name(*g_placeholder_name, next_placeholder_id())); }
static name const & to_prefix(expr_placeholder_kind k) {
    switch (k) {
    case expr_placeholder_kind::Implicit:       return *g_implicit_placeholder_name;
    case expr_placeholder_kind::StrictImplicit: return *g_strict_placeholder_name;
    case expr_placeholder_kind::Explicit:       return *g_explicit_placeholder_name;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
expr mk_expr_placeholder(optional<expr> const & type, expr_placeholder_kind k) {
    name n(to_prefix(k), next_placeholder_id());
    if (type)
        return mk_local(n, *type);
    else
        return mk_constant(n);
}
static bool is_placeholder(name const & n) {
    if (n.is_atomic())
        return false;
    name const & p = n.get_prefix();
    return p == *g_implicit_placeholder_name || p == *g_strict_placeholder_name || p == *g_explicit_placeholder_name;
}
static bool is_strict_placeholder(name const & n) {
    return !n.is_atomic() && n.get_prefix() == *g_strict_placeholder_name;
}
static bool is_explicit_placeholder(name const & n) {
    return !n.is_atomic() && n.get_prefix() == *g_explicit_placeholder_name;
}
bool is_placeholder(level const & e) { return is_global(e) && is_placeholder(global_id(e)); }
bool is_placeholder(expr const & e) {
    return (is_constant(e) && is_placeholder(const_name(e))) || (is_local(e) && is_placeholder(mlocal_name(e)));
}
bool is_strict_placeholder(expr const & e) {
    return (is_constant(e) && is_strict_placeholder(const_name(e))) || (is_local(e) && is_strict_placeholder(mlocal_name(e)));
}
bool is_explicit_placeholder(expr const & e) {
    return (is_constant(e) && is_explicit_placeholder(const_name(e))) || (is_local(e) && is_explicit_placeholder(mlocal_name(e)));
}
optional<expr> placeholder_type(expr const & e) {
    if (is_local(e) && is_placeholder(e))
        return some_expr(mlocal_type(e));
    else
        return none_expr();
}

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
static int mk_expr_placeholder(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_expr(L, mk_expr_placeholder());
    else
        return push_expr(L, mk_expr_placeholder(some_expr(to_expr(L, 1))));
}
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
static int placeholder_type(lua_State * L) { return push_optional_expr(L, placeholder_type(to_expr(L, 1))); }

void open_placeholder(lua_State * L) {
    SET_GLOBAL_FUN(mk_level_placeholder, "mk_level_placeholder");
    SET_GLOBAL_FUN(mk_expr_placeholder,  "mk_expr_placeholder");
    SET_GLOBAL_FUN(is_placeholder,       "is_placeholder");
    SET_GLOBAL_FUN(placeholder_type,     "placeholder_type");
    SET_GLOBAL_FUN(has_placeholder,      "has_placeholder");
}
}
