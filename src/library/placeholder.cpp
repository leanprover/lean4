/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/thread.h"
#include "kernel/find_fn.h"
#include "library/placeholder.h"
#include "library/pos_info_provider.h"

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
level mk_level_placeholder() { return mk_univ_param(name(*g_placeholder_name, next_placeholder_id())); }

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
bool is_placeholder(level const & e) { return is_param(e) && is_placeholder(param_id(e)); }

bool is_placeholder(expr const & e) {
    expr e2 = unwrap_pos(e);
    return (is_constant(e2) && is_placeholder(const_name(e2))) || (is_local(e2) && is_placeholder(local_name(e2)));
}
bool is_strict_placeholder(expr const & e) {
    expr e2 = unwrap_pos(e);
    return (is_constant(e2) && is_strict_placeholder(const_name(e2))) || (is_local(e2) && is_strict_placeholder(local_name(e2)));
}
bool is_explicit_placeholder(expr const & e) {
    expr e2 = unwrap_pos(e);
    return (is_constant(e2) && is_explicit_placeholder(const_name(e2))) || (is_local(e2) && is_explicit_placeholder(local_name(e2)));
}
optional<expr> placeholder_type(expr const & e) {
    expr e2 = unwrap_pos(e);
    if (is_local(e2) && is_placeholder(e2))
        return some_expr(local_type(e2));
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
}
