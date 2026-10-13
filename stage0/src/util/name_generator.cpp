/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include <limits>
#include "util/name_generator.h"
#include "util/name_set.h"

namespace lean {
static name_set * g_ngen_prefixes = nullptr;
static name * g_tmp_prefix = nullptr;

name_generator::name_generator(name const & prefix):m_prefix(prefix), m_next_idx(0) {
    lean_assert(!prefix.is_anonymous());
    lean_assert(uses_name_generator_prefix(prefix));
}

name_generator::name_generator():name_generator(*g_tmp_prefix) {}

name name_generator::next() {
    if (m_next_idx == std::numeric_limits<unsigned>::max()) {
        // avoid overflow
        m_prefix   = name(m_prefix, m_next_idx);
        m_next_idx = 0;
    }
    name r(m_prefix, m_next_idx);
    m_next_idx++;
    return r;
}

void register_name_generator_prefix(name const & n) {
    lean_assert(!g_ngen_prefixes->contains(n));
    g_ngen_prefixes->insert(n);
}

bool uses_name_generator_prefix(name const & n) {
    if (n.is_anonymous())
        return false;
    else if (g_ngen_prefixes->contains(n))
        return true;
    else
        return uses_name_generator_prefix(n.get_prefix());
}

void initialize_name_generator() {
    g_ngen_prefixes = new name_set();
    g_tmp_prefix    = new name("_uniq");
    mark_persistent(g_tmp_prefix->raw());
    register_name_generator_prefix(*g_tmp_prefix);
}

void finalize_name_generator() {
    delete g_tmp_prefix;
    delete g_ngen_prefixes;
}
}
