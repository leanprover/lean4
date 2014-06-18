/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <utility>
#include <string>
#include "util/thread.h"
#include "util/pair.h"
#include "util/script_state.h"

namespace lean {
static mutex g_code_mutex;
static std::vector<std::pair<bool, std::string>> g_code;
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
        g_code.push_back(mk_pair(true, code));
    }
}

/** \brief Import \c fname in all states in the pool */
void system_import(char const * fname) {
    {
        // Import file in all existing states
        lock_guard<mutex> lk(g_state_mutex);
        for (auto & s : g_states) {
            s.import_explicit(fname);
        }
    }
    {
        // Save module for future states
        lock_guard<mutex> lk(g_code_mutex);
        g_code.push_back(mk_pair(false, fname));
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
        for (auto const & p : g_code) {
            if (p.first)
                r.dostring(p.second.c_str());
            else
                r.import(p.second.c_str());
        }
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

// If reset == true,  then reset/release the (script_state) thread local storage
// If reset == false, then return (script_state) thread local
static script_state * get_script_state_ref(bool reset) {
    LEAN_THREAD_PTR(script_state_ref) g_thread_state;
    if (reset) {
        g_thread_state.reset(nullptr);
        return nullptr;
    } else {
        if (!g_thread_state.get())
            g_thread_state.reset(new script_state_ref());
        return &((*g_thread_state).m_state);
    }
}

script_state get_thread_script_state() { return *get_script_state_ref(false); }
void release_thread_script_state() { get_script_state_ref(true); }
}
