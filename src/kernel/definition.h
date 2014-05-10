/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <string>
#include "util/rc.h"
#include "kernel/expr.h"

namespace lean {
/**
    \brief Module index. The kernel provides only basic support
    for implementing a module system outside of the kernel.

    We need at least the notion of module index in the kernel, because
    it affects the convertability procedure.

    Given an opaque definition (non-theorem) d in module m1, then d is considered
    to be transparent for any other opaque definition in module m1.
*/
typedef unsigned module_idx;

/**
   \brief Environment definitions, theorems, axioms and variable declarations.
*/
class definition {
    struct cell;
    cell * m_ptr;
    explicit definition(cell * ptr);
    friend struct cell;
public:
    /**
       \brief The default constructor creates a reference to a "dummy"
       definition.  The actual "dummy" definition is not relevant, and
       no procedure should rely on the kind of definition used.

       We have a default constructor because some collections only work
       with types that have a default constructor.
    */
    definition();
    definition(definition const & s);
    definition(definition && s);
    ~definition();

    friend void swap(definition & a, definition & b) { std::swap(a.m_ptr, b.m_ptr); }

    definition & operator=(definition const & s);
    definition & operator=(definition && s);

    friend bool is_eqp(definition const & d1, definition const & d2) { return d1.m_ptr == d2.m_ptr; }

    bool is_definition() const;
    bool is_axiom() const;
    bool is_theorem() const;
    bool is_var_decl() const;

    name get_name() const;
    param_names const & get_params() const;
    expr get_type() const;

    expr get_value() const;
    bool is_opaque() const;
    unsigned get_weight() const;
    module_idx get_module_idx() const;
    bool use_conv_opt() const;

    friend definition mk_definition(environment const & env, name const & n, param_names const & params, expr const & t,
                                    expr const & v, bool opaque, module_idx mod_idx, bool use_conv_opt);
    friend definition mk_definition(name const & n, param_names const & params, expr const & t, expr const & v, bool opaque,
                                    unsigned weight, module_idx mod_idx, bool use_conv_opt);
    friend definition mk_theorem(name const & n, param_names const & params, expr const & t, expr const & v);
    friend definition mk_axiom(name const & n, param_names const & params, expr const & t);
    friend definition mk_var_decl(name const & n, param_names const & params, expr const & t);

    void write(serializer & s) const;
};

inline optional<definition> none_definition() { return optional<definition>(); }
inline optional<definition> some_definition(definition const & o) { return optional<definition>(o); }
inline optional<definition> some_definition(definition && o) { return optional<definition>(std::forward<definition>(o)); }

definition mk_definition(name const & n, param_names const & params, expr const & t, expr const & v,
                         bool opaque = false, unsigned weight = 0, module_idx mod_idx = 0, bool use_conv_opt = true);
definition mk_definition(environment const & env, name const & n, param_names const & params, expr const & t, expr const & v,
                         bool opaque = false, module_idx mod_idx = 0, bool use_conv_opt = true);
definition mk_theorem(name const & n, param_names const & params, expr const & t, expr const & v);
definition mk_axiom(name const & n, param_names const & params, expr const & t);
definition mk_var_decl(name const & n, param_names const & params, expr const & t);
}
