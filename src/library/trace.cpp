/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/sexpr/option_declarations.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/trace.h"

namespace lean {
static name_set *            g_trace_classes = nullptr;
static name_map<name_set>  * g_trace_aliases = nullptr;
MK_THREAD_LOCAL_GET_DEF(std::vector<name>, get_enabled_trace_classes);
MK_THREAD_LOCAL_GET_DEF(environment, get_dummy_env);
LEAN_THREAD_PTR(environment, g_env);
LEAN_THREAD_PTR(io_state,    g_ios);
LEAN_THREAD_VALUE(unsigned,  g_depth, 0);

void register_trace_class(name const & n) {
    register_option(name("trace") + n, BoolOption, "false", "(trace) enable/disable tracing for the given module and submodules");
    g_trace_classes->insert(n);
}

void register_trace_class_alias(name const & n, name const & alias) {
    name_set new_s;
    if (auto s = g_trace_aliases->find(n))
        new_s = *s;
    new_s.insert(alias);
    g_trace_aliases->insert(n, new_s);
}

bool is_trace_enabled() {
    return !get_enabled_trace_classes().empty();
}

void enable_trace_class(name const & c) {
    std::vector<name> & cs = get_enabled_trace_classes();
    if (std::find(cs.begin(), cs.end(), c) == cs.end())
        cs.push_back(c);
}

bool is_trace_class_enabled_core(name const & n) {
    for (name const & p : get_enabled_trace_classes()) {
        if (is_prefix_of(p, n))
            return true;
    }
    return false;
}

bool is_trace_class_enabled(name const & n) {
    if (!is_trace_enabled())
        return false;
    if (is_trace_class_enabled_core(n))
        return true;
    if (auto s = g_trace_aliases->find(n)) {
        bool found = false;
        s->for_each([&](name const & alias) {
                if (!found && is_trace_class_enabled_core(alias))
                    found = true;
            });
        if (found)
            return true;
    }
    return false;
}

scope_trace_env::scope_trace_env(environment const & env, io_state const & ios) {
    m_sz      = get_enabled_trace_classes().size();
    m_old_env = g_env;
    m_old_ios = g_ios;
    g_env     = const_cast<environment*>(&env);
    g_ios     = const_cast<io_state*>(&ios);
    name trace("trace");
    ios.get_options().for_each([&](name const & n) {
            if (is_prefix_of(trace, n)) {
                name cls        = n.replace_prefix(trace, name());
                enable_trace_class(cls);
            }
        });
}

scope_trace_env::~scope_trace_env() {
    g_env = const_cast<environment*>(m_old_env);
    g_ios = const_cast<io_state*>(m_old_ios);
    get_enabled_trace_classes().resize(m_sz);
}

void scope_trace_inc_depth::activate() {
    lean_assert(!m_active);
    m_active = true;
    g_depth++;
}

scope_trace_inc_depth::~scope_trace_inc_depth() {
    if (m_active)
        g_depth--;
}

io_state_stream tout() {
    if (g_env) {
        return diagnostic(*g_env, *g_ios);
    } else {
        return diagnostic(get_dummy_env(), get_dummy_ios());
    }
}

io_state_stream const & operator<<(io_state_stream const & ios, tdepth const &) {
    ios << g_depth << ". ";
    return ios;
}

io_state_stream const & operator<<(io_state_stream const & ios, tclass const & c) {
    ios << "[" << c.m_cls << "] ";
    return ios;
}

void initialize_trace() {
    g_trace_classes = new name_set();
    g_trace_aliases = new name_map<name_set>();
}

void finalize_trace() {
    delete g_trace_classes;
    delete g_trace_aliases;
}
}
