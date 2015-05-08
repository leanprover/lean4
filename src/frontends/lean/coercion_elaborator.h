/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "library/choice_iterator.h"

namespace lean {
/** \brief Abstract class for hiding details of the info_manager from the coercion_elaborator */
class coercion_info_manager {
public:
    virtual void erase_coercion_info(expr const & e) = 0;
    virtual void save_coercion_info(expr const & e, expr const & c) = 0;
};

class coercion_elaborator : public choice_iterator {
    coercion_info_manager & m_info;
    expr                    m_arg;
    bool                    m_id; // true if identity was not tried yet
    list<constraints>       m_choices;
    list<expr>              m_coercions;
public:
    coercion_elaborator(coercion_info_manager & info, expr const & arg,
                        list<constraints> const & choices, list<expr> const & coes,
                        bool use_id = true);
    optional<constraints> next();
};

/** \brief Given a term <tt>a : a_type</tt>, and a metavariable \c m, creates a constraint
    that considers coercions from a_type to the type assigned to \c m.

    This function is used when the types \c a_type and/or the type of \c m
    are not known at preprocessing time, and a choice function is used to
    enumerate coercion functions \c f. By "not known", we mean the type is a
    metavariable application.

    \see coercion_info_manager
*/
constraint mk_coercion_cnstr(type_checker & tc, coercion_info_manager & infom,
                             expr const & m, expr const & a, expr const & a_type,
                             justification const & j, unsigned delay_factor);

list<expr> get_coercions_from_to(type_checker & tc, expr const & from_type, expr const & to_type, constraint_seq & cs);
}
