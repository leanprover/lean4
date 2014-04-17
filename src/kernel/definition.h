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
   \brief Environment definitions, theorems, axioms and variable declarations.
*/
class definition {
    struct cell;
    cell * m_ptr;
    explicit definition(cell * ptr);
    friend class cell;
public:
    definition(definition const & s);
    definition(definition && s);
    ~definition();

    friend void swap(definition & a, definition & b) { std::swap(a.m_ptr, b.m_ptr); }

    definition & operator=(definition const & s);
    definition & operator=(definition && s);

    bool is_definition() const;
    bool is_axiom() const;
    bool is_theorem() const;
    bool is_var_decl() const;

    name get_name() const;
    param_names const & get_params() const;
    level_cnstrs const & get_level_cnstrs() const;
    expr get_type() const;

    expr get_value() const;
    bool is_opaque() const;
    unsigned get_weight() const;
    bool use_conv_opt() const;

    friend definition mk_definition(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t, expr const & v, bool opaque, unsigned weight, unsigned mod_idx, bool use_conv_opt);
    friend definition mk_theorem(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t, expr const & v);
    friend definition mk_axiom(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t);
    friend definition mk_var_decl(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t);

    void write(serializer & s) const;
};

inline optional<definition> none_definition() { return optional<definition>(); }
inline optional<definition> some_definition(definition const & o) { return optional<definition>(o); }
inline optional<definition> some_definition(definition && o) { return optional<definition>(std::forward<definition>(o)); }

definition mk_definition(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t, expr const & v, bool opaque = false, unsigned weight = 0, unsigned mod_idx = 0, bool use_conv_opt = true);
definition mk_theorem(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t, expr const & v);
definition mk_axiom(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t);
definition mk_var_decl(name const & n, param_names const & params, level_cnstrs const & cs, expr const & t);
}
