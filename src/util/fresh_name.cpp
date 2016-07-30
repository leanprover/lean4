/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/fresh_name.h"
#include "util/thread.h"

namespace lean {
MK_THREAD_LOCAL_GET_DEF(name, get_prefix);
LEAN_THREAD_VALUE(unsigned, g_next_idx, 0);

name mk_fresh_name() {
    name & prefix = get_prefix();
    if (prefix.is_anonymous()) {
        // prefix has not been initialized for this thread yet.
        prefix = name::mk_internal_unique_name();
    }
    if (g_next_idx == std::numeric_limits<unsigned>::max()) {
        // avoid overflow
        prefix = name(prefix, g_next_idx);
        g_next_idx = 0;
    }
    name r(prefix, g_next_idx);
    g_next_idx++;
    return r;
}

name mk_tagged_fresh_name(name const & tag) {
    lean_assert(tag.is_atomic());
    name & prefix = get_prefix();
    if (prefix.is_anonymous()) {
        // prefix has not been initialized for this thread yet.
        prefix = name::mk_internal_unique_name();
    }
    if (g_next_idx == std::numeric_limits<unsigned>::max()) {
        // avoid overflow
        prefix = name(prefix, g_next_idx);
        g_next_idx = 0;
    }
    name r(tag + prefix, g_next_idx);
    g_next_idx++;
    return r;
}

bool is_tagged_by(name const & n, name const & tag) {
    lean_assert(tag.is_atomic());
    if (n.is_atomic())
        return false;
    name t = n;
    while (!t.is_atomic())
        t = t.get_prefix();
    return t == tag;
}

/* A tagged name is of the form tag.unique_id.suffix */
optional<name> get_tagged_name_suffix(name const & n, name const & tag) {
    if (n.is_atomic()) {
        return optional<name>();
    } else if (n.get_prefix() == tag) {
        return optional<name>(name());
    } else if (auto new_prefix = get_tagged_name_suffix(n.get_prefix(), tag)) {
        if (n.is_string()) {
            return optional<name>(*new_prefix, n.get_string());
        } else {
            return optional<name>(*new_prefix, n.get_numeral());
        }
    } else {
        return optional<name>();
    }
}
}
