/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <utility>
#include <string>
#include <memory>
#include <iostream>
#include "util/thread.h"
#include "util/pair.h"
#include "util/script_state.h"

namespace lean {
struct script_state_manager {
    mutex                                m_code_mutex;
    std::vector<pair<bool, std::string>> m_code;
    mutex                                m_state_mutex;
    std::vector<script_state>            m_states;
    std::vector<script_state>            m_available_states;
    script_state_manager() {}
    ~script_state_manager() {}
};

static script_state_manager * g_manager = nullptr;

void initialize_thread_script_state() {
    g_manager = new script_state_manager();
}

void finalize_thread_script_state() {
    delete g_manager;
    g_manager = nullptr;
}

static script_state_manager & get_script_state_manager() {
    return *g_manager;
}

static bool is_manager_alive() { return g_manager; }

/** \brief Execute \c code in all states in the pool */
void system_dostring(char const * code) {
    script_state_manager & m = get_script_state_manager();
    {
        // Execute code in all existing states
        lock_guard<mutex> lk(m.m_state_mutex);
        for (auto & s : m.m_states) {
            s.dostring(code);
        }
    }
    {
        // Save code for future states
        lock_guard<mutex> lk(m.m_code_mutex);
        m.m_code.push_back(mk_pair(true, code));
    }
}

/** \brief Import \c fname in all states in the pool */
void system_import(char const * fname) {
    script_state_manager & m = get_script_state_manager();
    {
        // Import file in all existing states
        lock_guard<mutex> lk(m.m_state_mutex);
        for (auto & s : m.m_states) {
            s.import_explicit(fname);
        }
    }
    {
        // Save module for future states
        lock_guard<mutex> lk(m.m_code_mutex);
        m.m_code.push_back(mk_pair(false, fname));
    }
}

static script_state get_state() {
    script_state_manager & m = get_script_state_manager();
    {
        // Try to reuse existing state
        lock_guard<mutex> lk(m.m_state_mutex);
        if (!m.m_available_states.empty()) {
            script_state r(m.m_available_states.back());
            m.m_available_states.pop_back();
            return r;
        }
    }

    {
        // Execute existing code in new state
        lock_guard<mutex> lk(m.m_code_mutex);
        script_state r;
        for (auto const & p : m.m_code) {
            if (p.first)
                r.dostring(p.second.c_str());
            else
                r.import_explicit(p.second.c_str());
        }
        {
            // save new state in vector of all states
            lock_guard<mutex> lk(m.m_state_mutex);
            m.m_states.push_back(r);
        }
        return r;
    }
}

static void recycle_state(script_state s) {
    if (is_manager_alive()) {
        script_state_manager & m = get_script_state_manager();
        lock_guard<mutex> lk(m.m_state_mutex);
        m.m_available_states.push_back(s);
    }
}

struct script_state_ref {
    script_state m_state;
    script_state_ref():m_state(get_state()) {}
    ~script_state_ref() { recycle_state(m_state); }
};

LEAN_THREAD_PTR(bool, g_registered);
LEAN_THREAD_PTR(script_state_ref, g_thread_state_ref);

static void finalize_thread_state_ref() {
    delete g_thread_state_ref;
    g_thread_state_ref = nullptr;
    delete g_registered;
    g_registered = nullptr;
}

script_state get_thread_script_state() {
    if (!g_thread_state_ref) {
        g_thread_state_ref = new script_state_ref();
        if (!g_registered) {
            g_registered = new bool(true);
            register_thread_finalizer(finalize_thread_state_ref);
        }
    }
    return g_thread_state_ref->m_state;
}

void release_thread_script_state() {
    delete g_thread_state_ref;
    g_thread_state_ref = nullptr;
}
}
