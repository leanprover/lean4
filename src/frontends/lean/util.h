/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
class parser;
void check_atomic(name const & n);
void check_in_section(parser const & p);
bool is_root_namespace(name const & n);
name remove_root_prefix(name const & n);
/** \brief Copy the parameters associated with the local names in \c local_names to \c section_ps.
    Then sort \c section_ps (using the order in which they were declared).
*/
void mk_section_params(name_set const & local_names, parser const & p, buffer<expr> & section_ps);
/** \brief Return the levels in \c ls that are defined in the section. */
levels collect_section_levels(level_param_names const & ls, parser & p);
/** \brief Collect local (section) constants occurring in type and value, sort them, and store in section_ps */
void collect_section_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & section_ps);
}
