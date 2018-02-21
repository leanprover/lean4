/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include <limits>
#include "util/thread.h"
#include "util/exception.h"
#include "library/unique_id.h"

namespace lean {
static unsigned g_next_thread_id       = 0;
static mutex *  g_next_thread_id_guard = nullptr;

LEAN_THREAD_VALUE(unsigned, g_thread_id, std::numeric_limits<unsigned>::max());
LEAN_THREAD_VALUE(unsigned, g_next_idx, 0);

unique_id::unique_id():
    m_thread_id(std::numeric_limits<unsigned>::max()),
    m_id(0) {
}

bool unique_id::is_valid() const {
    return m_thread_id != std::numeric_limits<unsigned>::max();
}

unique_id mk_unique_id() {
    if (g_thread_id == std::numeric_limits<unsigned>::max()) {
        lock_guard<mutex> lock(*g_next_thread_id_guard);
        g_thread_id = g_next_thread_id;
        g_next_thread_id++;
        if (g_next_thread_id == std::numeric_limits<unsigned>::max()) {
            g_next_thread_id--;
            throw exception("failed to generate unique id, too many threads");
        }
    }
    unique_id r(g_thread_id, g_next_idx);
    g_next_idx++;
    if (g_next_idx == std::numeric_limits<unsigned>::max()) {
        g_next_idx--;
        throw exception("failed to generate unique unique id, too many ids have been generated");
    }
    return r;
}

void initialize_unique_id() {
    g_next_thread_id_guard = new mutex();
    register_thread_local_reset_fn([]() { g_next_idx = 0; });
}

void finalize_unique_id() {
    delete g_next_thread_id_guard;
}
}
