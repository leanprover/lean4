/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include <limits>
#include <algorithm>
#include "util/name_generator.h"

namespace lean {
static name * g_tmp_prefix = nullptr;
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

void swap(name_generator & a, name_generator & b) {
    swap(a.m_prefix, b.m_prefix);
    std::swap(a.m_next_idx, b.m_next_idx);
}

void initialize_name_generator() {
    g_tmp_prefix = new name("_uniq");
}

void finalize_name_generator() {
    delete g_tmp_prefix;
}
}
