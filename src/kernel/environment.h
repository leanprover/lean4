/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <memory>
#include <vector>
#include "runtime/optional.h"
#include "util/rc.h"
#include "util/list.h"
#include "util/rb_map.h"
#include "util/name_set.h"
#include "util/name_map.h"
#include "kernel/expr.h"
#include "kernel/declaration.h"

#ifndef LEAN_BELIEVER_TRUST_LEVEL
/* If an environment E is created with a trust level > LEAN_BELIEVER_TRUST_LEVEL, then
   we can add declarations to E without type checking them. */
#define LEAN_BELIEVER_TRUST_LEVEL 1024
#endif

namespace lean {
class environment_extension {
public:
    virtual ~environment_extension() {}
};

class environment : public object_ref {
    friend class add_inductive_fn;

    void check_name(name const & n) const;
    void check_duplicated_univ_params(names ls) const;

    void add_core(constant_info const & info);
    void mark_quot_initialized();
    environment add(constant_info const & info) const;
    environment add_axiom(declaration const & d, bool check) const;
    environment add_definition(declaration const & d, bool check) const;
    environment add_theorem(declaration const & d, bool check) const;
    environment add_opaque(declaration const & d, bool check) const;
    environment add_mutual(declaration const & d, bool check) const;
    environment add_quot() const;
    environment add_inductive(declaration const & d) const;
public:
    environment(unsigned trust_lvl = 0);
    environment(environment const & other):object_ref(other) {}
    environment(environment && other):object_ref(other) {}
    explicit environment(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit environment(obj_arg o):object_ref(o) {}
    ~environment() {}

    environment & operator=(environment const & other) { object_ref::operator=(other); return *this; }
    environment & operator=(environment && other) { object_ref::operator=(other); return *this; }

    /** \brief Return the trust level of this environment. */
    unsigned trust_lvl() const;

    bool is_quot_initialized() const;

    void set_main_module(name const & n);

    name get_main_module() const;

    /** \brief Return information for the constant with name \c n (if it is defined in this environment). */
    optional<constant_info> find(name const & n) const;

    /** \brief Return information for the constant with name \c n. Throws and exception if constant declaration does not exist in this environment. */
    constant_info get(name const & n) const;

    /** \brief Extends the current environment with the given declaration */
    environment add(declaration const & d, bool check = true) const;

    /** \brief Apply the function \c f to each constant */
    void for_each_constant(std::function<void(constant_info const & d)> const & f) const;

    /** \brief Pointer equality */
    friend bool is_eqp(environment const & e1, environment const & e2) {
        return e1.raw() == e2.raw();
    }

    void display_stats() const;
};

void check_no_metavar_no_fvar(environment const & env, name const & n, expr const & e);

void initialize_environment();
void finalize_environment();
}
