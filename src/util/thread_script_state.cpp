/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/thread.h"
#include "util/script_state.h"

namespace lean {
static mutex g_code_mutex;
static std::vector<std::string>  g_code;
static mutex g_state_mutex;
static std::vector<script_state> g_states;
static std::vector<script_state> g_available_states;

/** \brief Execute \c code in all states in the pool */
void system_dostring(char const * code) {
    {
        // Execute code in all existing states
        lock_guard<mutex> lk(g_state_mutex);
        for (auto & s : g_states) {
            s.dostring(code);
        }
    }
    {
        // Save code for future states
        lock_guard<mutex> lk(g_code_mutex);
        g_code.push_back(code);
    }
}

static script_state get_state() {
    {
        // Try to reuse existing state
        lock_guard<mutex> lk(g_state_mutex);
        if (!g_available_states.empty()) {
            script_state r(g_available_states.back());
            g_available_states.pop_back();
            return r;
        }
    }

    {
        // Execute existing code in new state
        lock_guard<mutex> lk(g_code_mutex);
        script_state r;
        for (auto & c : g_code)
            r.dostring(c.c_str());
        g_states.push_back(r);
        {
            // save new state in vector of all states
            lock_guard<mutex> lk(g_state_mutex);
            g_states.push_back(r);
        }
        return r;
    }
}

static void recycle_state(script_state s) {
    lock_guard<mutex> lk(g_state_mutex);
    g_available_states.push_back(s);
}

struct script_state_ref {
    script_state m_state;
    script_state_ref():m_state(get_state()) {}
    ~script_state_ref() { recycle_state(m_state); }
};

// We should use std::unique_ptr, but clang++ 3.3.1 crashes when we use it.
std::shared_ptr<script_state_ref> LEAN_THREAD_LOCAL g_thread_state;

script_state get_thread_script_state() {
    if (!g_thread_state)
        g_thread_state = std::make_shared<script_state_ref>();
    return g_thread_state->m_state;
}

void release_thread_script_state() {
    g_thread_state = nullptr;
}
}
