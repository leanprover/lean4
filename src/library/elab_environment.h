/*
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/* Wrapper for `Lean.Environment` */
class LEAN_EXPORT elab_environment : public object_ref {
public:
    elab_environment(elab_environment const & other):object_ref(other) {}
    elab_environment(elab_environment && other):object_ref(other) {}
    explicit elab_environment(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit elab_environment(obj_arg o):object_ref(o) {}
    ~elab_environment() {}

    elab_environment & operator=(elab_environment const & other) { object_ref::operator=(other); return *this; }
    elab_environment & operator=(elab_environment && other) { object_ref::operator=(other); return *this; }

    /** \brief Return information for the constant with name \c n (if it is defined in this environment). */
    optional<constant_info> find(name const & n) const { return to_kernel_env().find(n); };

    /** \brief Return information for the constant with name \c n. Throws and exception if constant declaration does not exist in this environment. */
    constant_info get(name const & n) const { return to_kernel_env().get(n); };

    /** \brief Extends the current environment with the given declaration */
    elab_environment add(declaration const & d, bool check = true) const;

    /** \brief Pointer equality */
    friend bool is_eqp(elab_environment const & e1, elab_environment const & e2) {
        return e1.raw() == e2.raw();
    }

    void display_stats() const;

    environment to_kernel_env() const;

    operator environment() const { return to_kernel_env(); }
};
}
