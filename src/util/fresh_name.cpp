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
static name * g_fresh = nullptr;
MK_THREAD_LOCAL_GET_DEF(std::unique_ptr<name_generator>, get_name_generator_ptr);

name mk_fresh_name() {
    std::unique_ptr<name_generator> & ngen = get_name_generator_ptr();
    if (!ngen) {
        name unique = name::mk_internal_unique_name();
        ngen.reset(new name_generator(*g_fresh + unique));
    }
    return ngen->next();
}

bool is_fresh_name(name const & n) {
    if (n.is_anonymous() || !n.is_numeral())
        return false;
    else if (n.get_prefix() == *g_fresh)
        return true;
    else
        return is_fresh_name(n.get_prefix());
}

static void sanitize_fresh(sstream & strm, name const & n) {
    if (n.is_anonymous() || n == *g_fresh) {
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
    return tag + mk_fresh_name();
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
    g_fresh = new name("_fresh");
    register_name_generator_prefix(*g_fresh);
}

void finalize_fresh_name() {
    delete g_fresh;
}
}
