/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/sstream.h"
#include "util/name_set.h"
#include "util/fresh_name.h"
#include "util/thread.h"
#include "util/shared_mutex.h"

namespace lean {
static name_set *     g_fresh_name_prefixes = nullptr;
static shared_mutex * g_fresh_name_prefixes_guard = nullptr;

static void register_fresh_name_prefix(name const & p) {
    exclusive_lock lock(*g_fresh_name_prefixes_guard);
    g_fresh_name_prefixes->insert(p);
}

/* CACHE_RESET: NO */
MK_THREAD_LOCAL_GET_DEF(name, get_prefix);
/* CACHE_RESET: YES */
LEAN_THREAD_VALUE(unsigned, g_next_idx, 0);

static bool is_fresh_prefix(name const & p) {
    if (p == get_prefix())
        return true;
    shared_lock lock(*g_fresh_name_prefixes_guard);
    return g_fresh_name_prefixes->contains(p);
};

name mk_fresh_name() {
    name & prefix = get_prefix();
    if (prefix.is_anonymous()) {
        // prefix has not been initialized for this thread yet.
        prefix = name::mk_internal_unique_name();
        register_fresh_name_prefix(prefix);
    }
    /* REMARK: after we implement RESET operation we will not need the following test anymore */
    if (g_next_idx == std::numeric_limits<unsigned>::max()) {
        // avoid overflow
        prefix = name(prefix, g_next_idx);
        register_fresh_name_prefix(prefix);
        g_next_idx = 0;
    }
    name r(prefix, g_next_idx);
    g_next_idx++;
    return r;
}

bool is_fresh_name(name const & n) {
    if (n.is_anonymous() || !n.is_numeral())
        return false;
    else if (is_fresh_prefix(n.get_prefix()))
        return true;
    else
        return is_fresh_name(n.get_prefix());
}

static void sanitize_fresh(sstream & strm, name const & n) {
    if (n.is_anonymous()) {
        strm << "_fresh";
    } else if (n.is_numeral()) {
        sanitize_fresh(strm, n.get_prefix());
        strm << "_" << n.get_numeral();
    } else {
        lean_unreachable();
    }
}

name sanitize_if_fresh(name const & n) {
    if (!is_fresh_name(n))
        return n;
    sstream strm;
    sanitize_fresh(strm, n);
    return name(strm.str());
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
            return optional<name>(name(*new_prefix, n.get_string()));
        } else {
            return optional<name>(name(*new_prefix, n.get_numeral()));
        }
    } else {
        return optional<name>();
    }
}

void initialize_fresh_name() {
    g_fresh_name_prefixes = new name_set();
    g_fresh_name_prefixes_guard = new shared_mutex();
}

void finalize_fresh_name() {
    delete g_fresh_name_prefixes;
    delete g_fresh_name_prefixes_guard;
}
}
