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
#include "stdlib_flags.h"

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

/* getDefaultVerbose (_ : Unit) : Bool */
extern "C" LEAN_EXPORT uint8 lean_internal_get_default_verbose(obj_arg) {
    return LEAN_DEFAULT_VERBOSE;
}

/* getDefaultOptions (_ : Unit) : Options */
extern "C" LEAN_EXPORT obj_res lean_internal_get_default_options(obj_arg) {
    return get_default_options().steal();
}

extern "C" LEAN_EXPORT obj_res lean_options_get_empty(obj_arg u);
options::options(): object_ref(lean_options_get_empty(box(0))) {}

extern "C" LEAN_EXPORT bool lean_options_get_bool(obj_arg opts, obj_arg n, bool default_value);
bool options::get_bool(name const & n, bool default_value) const {
    return lean_options_get_bool(this->to_obj_arg(), n.to_obj_arg(), default_value);
}

extern "C" LEAN_EXPORT obj_res lean_options_update_bool(obj_arg opts, obj_arg n, bool v);
options options::update(name const & n, bool v) const {
    return options(lean_options_update_bool(this->to_obj_arg(), n.to_obj_arg(), v));
}
}
