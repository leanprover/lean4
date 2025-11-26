/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include "runtime/sstream.h"
#include "util/options.h"
#include "util/option_declarations.h"

#ifndef LEAN_DEFAULT_VERBOSE
#define LEAN_DEFAULT_VERBOSE true
#endif

namespace lean {
static name * g_verbose    = nullptr;
static name * g_max_memory = nullptr;
static name * g_timeout    = nullptr;

void initialize_options() {
    g_verbose    = new name("verbose");
    mark_persistent(g_verbose->raw());
    g_max_memory = new name("max_memory");
    mark_persistent(g_max_memory->raw());
    g_timeout    = new name("timeout");
    mark_persistent(g_timeout->raw());
}

void finalize_options() {
    delete g_verbose;
    delete g_max_memory;
    delete g_timeout;
}

name const & get_verbose_opt_name() {
    return *g_verbose;
}

name const & get_max_memory_opt_name() {
    return *g_max_memory;
}

name const & get_timeout_opt_name() {
    return *g_timeout;
}

bool get_verbose(options const & opts) {
    return opts.get_bool(*g_verbose, LEAN_DEFAULT_VERBOSE);
}

options join(options const & opts1, options const & opts2) {
    kvmap r = opts2.m_value;
    for (kvmap_entry const & e : opts1.m_value) {
        if (!opts2.contains(e.fst())) {
            r = cons(e, r);
        }
    }
    return options(r);
}

void options::for_each(std::function<void(name const &)> const & fn) const {
    for (kvmap_entry const & e : m_value) {
        fn(e.fst());
    }
}
}
