/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/io.h"
#include "util/option_declarations.h"
#include "library/elab_environment.h"
#include "kernel/local_ctx.h"
#include "kernel/trace.h"

namespace lean {
LEAN_THREAD_PTR(const options,               g_opts);

void register_trace_class(name const & n, name const & decl_name) {
    register_option(name("trace") + n, decl_name, data_value_kind::Bool, "false",
                    "(trace) enable/disable tracing for the given module and submodules");
}

extern "C" bool lean_is_trace_class_enabled(obj_arg opts, obj_arg cls);
bool is_trace_class_enabled(name const & n) {
    return lean_is_trace_class_enabled(g_opts->to_obj_arg(), n.to_obj_arg());
}


scope_trace_env::scope_trace_env(elab_environment const & env, options const & o) {
    m_old_opts = g_opts;
    g_opts = &o;
}

scope_trace_env::~scope_trace_env() {
    g_opts = const_cast<options*>(m_old_opts);
}

extern "C" obj_res lean_io_eprint(obj_arg s);
static void io_eprint(obj_arg s) {
    object * r = lean_io_eprint(s);
    if (!lean_io_result_is_ok(r))
        lean_io_result_show_error(r);
    lean_dec(r);
}

tout::~tout() {
    io_eprint(mk_string(m_out.str()));
}

std::ostream & operator<<(std::ostream & ios, tclass const & c) {
    ios << "[" << c.m_cls << "] ";
    return ios;
}

void initialize_trace() {
}

void finalize_trace() {
}

}
