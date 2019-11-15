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
static name * g_placeholder_name          = nullptr;

void initialize_placeholder() {
    g_placeholder_name = new name(name::mk_internal_unique_name(), "_");
}

void finalize_placeholder() {
    delete g_placeholder_name;
}

level mk_level_placeholder() { return mk_univ_mvar(name()); }

expr mk_expr_placeholder() {
    return mk_mvar(name());
}
static bool is_placeholder(name const & n) {
    return n.is_anonymous();
}
bool is_placeholder(level const & e) { return is_mvar(e) && is_placeholder(mvar_id(e)); }

bool is_placeholder(expr const & e) {
    expr e2 = unwrap_pos(e);
    return is_mvar(e2) && is_placeholder(mvar_name(e2));
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
