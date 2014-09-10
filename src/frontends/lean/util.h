/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "frontends/lean/local_decls.h"
namespace lean {
class parser;
void check_atomic(name const & n);
void check_in_section_or_context(parser const & p);
bool is_root_namespace(name const & n);
name remove_root_prefix(name const & n);
/** \brief Return the levels in \c ls that are defined in the section. */
levels collect_section_levels(level_param_names const & ls, parser & p);
/** \brief Collect local (section) constants occurring in type and value, sort them, and store in section_ps */
void collect_section_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & section_ps);
/** \brief Copy the local parameters to \c section_ps, then sort \c section_ps (using the order in which they were declared). */
void sort_section_params(expr_struct_set const & locals, parser const & p, buffer<expr> & section_ps);
list<expr> locals_to_context(expr const & e, parser const & p);
/** \brief Fun(locals, e), but also propagate \c e position to result */
expr Fun(buffer<expr> const & locals, expr const & e, parser & p);
/** \brief Pi(locals, e), but also propagate \c e position to result */
expr Pi(buffer<expr> const & locals, expr const & e, parser & p);
/** \brief Similar to Fun(locals, e, p), but the types are marked as 'as-is' (i.e., they are not processed by the elaborator. */
expr Fun_as_is(buffer<expr> const & locals, expr const & e, parser & p);
/** \brief Similar to Pi(locals, e, p), but the types are marked as 'as-is' (i.e., they are not processed by the elaborator. */
expr Pi_as_is(buffer<expr> const & locals, expr const & e, parser & p);
/** \brief Create the resultant universe level using the levels computed during introduction rule elaboration */
level mk_result_level(environment const & env, buffer<level> const & r_lvls);
/** \brief Return true if \c u occurs in \c l */
bool occurs(level const & u, level const & l);

/** \brief Convert the universe metavariables in \c e in new universe parameters.
    The substitution \c s is updated with the mapping metavar -> new param.
    The set of parameter names \c ps and the buffer \c new_ps are also updated.
*/
expr univ_metavars_to_params(environment const & env, local_decls<level> const & lls, substitution & s,
                             name_set & ps, buffer<name> & new_ps, expr const & e);
}
