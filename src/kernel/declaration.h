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
class declaration {
    struct cell;
    cell * m_ptr;
    explicit declaration(cell * ptr);
    friend struct cell;
public:
    /**
       \brief The default constructor creates a reference to a "dummy"
       declaration.  The actual "dummy" declaration is not relevant, and
       no procedure should rely on the kind of declaration used.

       We have a default constructor because some collections only work
       with types that have a default constructor.
    */
    declaration();
    declaration(declaration const & s);
    declaration(declaration && s);
    ~declaration();

    friend void swap(declaration & a, declaration & b) { std::swap(a.m_ptr, b.m_ptr); }

    declaration & operator=(declaration const & s);
    declaration & operator=(declaration && s);

    friend bool is_eqp(declaration const & d1, declaration const & d2) { return d1.m_ptr == d2.m_ptr; }

    bool is_definition() const;
    bool is_axiom() const;
    bool is_theorem() const;
    bool is_var_decl() const;

    name get_name() const;
    level_param_names const & get_params() const;
    expr get_type() const;

    expr get_value() const;
    bool is_opaque() const;
    unsigned get_weight() const;
    module_idx get_module_idx() const;
    bool use_conv_opt() const;

    friend declaration mk_definition(environment const & env, name const & n, level_param_names const & params, expr const & t,
                                    expr const & v, bool opaque, module_idx mod_idx, bool use_conv_opt);
    friend declaration mk_definition(name const & n, level_param_names const & params, expr const & t, expr const & v, bool opaque,
                                    unsigned weight, module_idx mod_idx, bool use_conv_opt);
    friend declaration mk_theorem(name const & n, level_param_names const & params, expr const & t, expr const & v);
    friend declaration mk_axiom(name const & n, level_param_names const & params, expr const & t);
    friend declaration mk_var_decl(name const & n, level_param_names const & params, expr const & t);
};

inline optional<declaration> none_declaration() { return optional<declaration>(); }
inline optional<declaration> some_declaration(declaration const & o) { return optional<declaration>(o); }
inline optional<declaration> some_declaration(declaration && o) { return optional<declaration>(std::forward<declaration>(o)); }

declaration mk_definition(name const & n, level_param_names const & params, expr const & t, expr const & v,
                         bool opaque = false, unsigned weight = 0, module_idx mod_idx = 0, bool use_conv_opt = true);
declaration mk_definition(environment const & env, name const & n, level_param_names const & params, expr const & t, expr const & v,
                         bool opaque = false, module_idx mod_idx = 0, bool use_conv_opt = true);
declaration mk_theorem(name const & n, level_param_names const & params, expr const & t, expr const & v);
declaration mk_axiom(name const & n, level_param_names const & params, expr const & t);
declaration mk_var_decl(name const & n, level_param_names const & params, expr const & t);
}
