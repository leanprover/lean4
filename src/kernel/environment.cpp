/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <limits>
#include "runtime/sstream.h"
#include "runtime/thread.h"
#include "runtime/sharecommon.h"
#include "util/io.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"

namespace lean {
extern "C" object* lean_environment_find(object*, object*);
extern "C" uint8 lean_environment_quot_init(object*);
extern "C" object* lean_kernel_record_unfold (object*, object*);
extern "C" object* lean_kernel_get_diag(object*);
extern "C" object* lean_kernel_set_diag(object*, object*);
extern "C" uint8 lean_kernel_diag_is_enabled(object*);

void diagnostics::record_unfold(name const & decl_name) {
    m_obj = lean_kernel_record_unfold(m_obj, decl_name.to_obj_arg());
}

scoped_diagnostics::scoped_diagnostics(environment const & env, bool collect) {
    if (collect) {
        diagnostics d(env.get_diag());
        if (lean_kernel_diag_is_enabled(d.to_obj_arg())) {
            m_diag = new diagnostics(d);
        } else
            m_diag = nullptr;
    } else {
        m_diag = nullptr;
    }
}

scoped_diagnostics::~scoped_diagnostics() {
    if (m_diag)
        delete m_diag;
}

environment scoped_diagnostics::update(environment const & env) const {
    if (m_diag)
        return env.set_diag(*m_diag);
    else
        return env;
}

diagnostics environment::get_diag() const {
    return diagnostics(lean_kernel_get_diag(to_obj_arg()));
}

environment environment::set_diag(diagnostics const & diag) const {
    return environment(lean_kernel_set_diag(to_obj_arg(), diag.to_obj_arg()));
}

bool environment::is_quot_initialized() const {
    return lean_environment_quot_init(to_obj_arg()) != 0;
}

optional<constant_info> environment::find(name const & n) const {
    return to_optional<constant_info>(lean_environment_find(to_obj_arg(), n.to_obj_arg()));
}

constant_info environment::get(name const & n) const {
    object * o = lean_environment_find(to_obj_arg(), n.to_obj_arg());
    if (is_scalar(o))
        throw unknown_constant_exception(*this, n);
    constant_info r(cnstr_get(o, 0), true);
    dec(o);
    return r;
}

/* `lean_add_decl`, `lean_add_decl_without_checking`, `lean_elab_add_decl`,
   `lean_elab_add_decl_without_checking` and `lean_kernel_{is_def_eq,whnf,check}` are
   implemented in Lean by the InLean kernel (`src/Lean/Kernel/InLean/AddDecl.lean`). */

void initialize_environment() {
}

void finalize_environment() {
}
}
