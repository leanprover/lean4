/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "frontends/lean/local_context.h"

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

/** \brief Create a metavariable, and attach choice constraint for generating
    coercions of the form <tt>f a</tt>, where \c f is registered coercion,
    and \c a is the input argument that has type \c a_type, but is expected
    to have type \c expected_type because of \c j.

    This function is used when the types \c a_type and/or \c expected_type
    are not known at preprocessing time, and a choice function is used to
    enumerate coercion functions \c f.

    \param relax True if opaque constants in the current module should be treated
                 as transparent

    \see coercion_info_manager
*/
pair<expr, constraint> mk_coercion_elaborator(
    type_checker & tc, coercion_info_manager & infom, local_context & ctx, bool relax,
    expr const & a, expr const & a_type, expr const & expected_type, justification const & j);

pair<expr, constraint> coercions_to_choice(coercion_info_manager & infom, local_context & ctx,
                                           list<expr> const & coes, expr const & a,
                                           justification const & j, bool relax);
}
