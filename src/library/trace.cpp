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
MK_THREAD_LOCAL_GET_DEF(std::vector<name>, get_disabled_trace_classes);
MK_THREAD_LOCAL_GET_DEF(environment, get_dummy_env);
LEAN_THREAD_PTR(environment, g_env);
LEAN_THREAD_PTR(io_state,    g_ios);
LEAN_THREAD_VALUE(unsigned,  g_depth, 0);

void register_trace_class(name const & n) {
    register_option(name("trace") + n, BoolOption, "false",
                    "(trace) enable/disable tracing for the given module and submodules");
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

static void update_class(std::vector<name> & cs, name const & c) {
    if (std::find(cs.begin(), cs.end(), c) == cs.end()) {
        cs.push_back(c);
    }
}


static void enable_trace_class(name const & c) {
    update_class(get_enabled_trace_classes(), c);
}

static void disable_trace_class(name const & c) {
    update_class(get_disabled_trace_classes(), c);
}

static bool is_trace_class_set_core(std::vector<name> const & cs, name const & n) {
    for (name const & p : cs) {
        if (is_prefix_of(p, n)) {
            return true;
        }
    }
    return false;
}

static bool is_trace_class_set(std::vector<name> const & cs, name const & n) {
    if (is_trace_class_set_core(cs, n))
        return true;
    auto it = n;
    while (true) {
        if (auto s = g_trace_aliases->find(it)) {
            bool found = false;
            s->for_each([&](name const & alias) {
                    if (!found && is_trace_class_set_core(cs, alias))
                        found = true;
                });
            if (found)
                return true;
        }
        if (it.is_atomic())
            return false;
        it = it.get_prefix();
    }
}

bool is_trace_class_enabled(name const & n) {
    if (!is_trace_enabled())
        return false;
    if (is_trace_class_set(get_disabled_trace_classes(), n))
        return false; // it was explicitly disabled
    return is_trace_class_set(get_enabled_trace_classes(), n);
}

scope_trace_env::scope_trace_env(environment const & env, io_state const & ios) {
    m_enable_sz  = get_enabled_trace_classes().size();
    m_disable_sz = get_disabled_trace_classes().size();
    m_old_env    = g_env;
    m_old_ios    = g_ios;
    g_env        = const_cast<environment*>(&env);
    g_ios        = const_cast<io_state*>(&ios);
    options const & opts = ios.get_options();
    name trace("trace");
    opts.for_each([&](name const & n) {
            if (is_prefix_of(trace, n)) {
                name cls        = n.replace_prefix(trace, name());
                if (opts.get_bool(n, false))
                    enable_trace_class(cls);
                else
                    disable_trace_class(cls);
            }
        });
}

scope_trace_env::~scope_trace_env() {
    g_env = const_cast<environment*>(m_old_env);
    g_ios = const_cast<io_state*>(m_old_ios);
    get_enabled_trace_classes().resize(m_enable_sz);
    get_disabled_trace_classes().resize(m_disable_sz);
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

void scope_trace_init_bool_option::init(name const & n, bool v) {
    m_old_ios = g_ios;
    if (g_env && g_ios) {
        m_tmp_ios.reset(new io_state(*g_ios));
        options o = m_tmp_ios->get_options();
        o         = o.update_if_undef(n, v);
        m_tmp_ios->set_options(o);
        g_ios     = m_tmp_ios.get();
    }
}

scope_trace_init_bool_option::~scope_trace_init_bool_option() {
    if (m_tmp_ios) {
        g_ios = const_cast<io_state*>(m_old_ios);
    }
}

struct silent_ios_helper {
    std::shared_ptr<output_channel> m_out;
    io_state                        m_ios;
    silent_ios_helper():
        m_out(new null_output_channel()),
        m_ios(get_dummy_ios(), m_out, m_out) {}
};

MK_THREAD_LOCAL_GET_DEF(silent_ios_helper, get_silent_ios_helper);

scope_trace_silent::scope_trace_silent(bool flag) {
    m_old_ios = g_ios;
    if (flag)
        g_ios     = &get_silent_ios_helper().m_ios;
}

scope_trace_silent::~scope_trace_silent() {
    g_ios     = m_old_ios;
}

io_state_stream tout() {
    if (g_env) {
        return diagnostic(*g_env, *g_ios);
    } else {
        return diagnostic(get_dummy_env(), get_silent_ios_helper().m_ios);
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

    register_trace_class(name{"debug"});
}

void finalize_trace() {
    delete g_trace_classes;
    delete g_trace_aliases;
}
}
