/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "kernel/type_checker.h"
#include "frontends/lean/local_decls.h"
namespace lean {
class parser;
typedef std::unique_ptr<type_checker> type_checker_ptr;

/** \brief Parse optional '[persistent]' modifier.
    return true if it is was found, and paremeter \c persistent to true.
*/
bool parse_persistent(parser & p, bool & persistent);

void check_atomic(name const & n);
void check_in_section_or_context(parser const & p);
bool is_root_namespace(name const & n);
name remove_root_prefix(name const & n);
/** \brief Return the levels in \c ls that are defined in the section, but are not tagged as variables. */
levels collect_section_nonvar_levels(parser & p, level_param_names const & ls);
/** \brief Collect local (section) constants occurring in type and value, sort them, and store in section_ps */
void collect_section_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & section_ps);
/** \brief Copy the local parameters to \c section_ps, then sort \c section_ps (using the order in which they were declared). */
void sort_section_params(expr_struct_set const & locals, parser const & p, buffer<expr> & section_ps);
/** \brief Remove from \c ps local constants that are tagged as section variables. */
void remove_section_variables(parser const & p, buffer<expr> & ps);
list<expr> locals_to_context(expr const & e, parser const & p);
/** \brief Create the term <tt>(@^-1 (@n.{sec_ls} @sec_params[0] ... @sec_params[num_sec_params-1]))</tt>
    When we declare \c n inside of a section, the section parameters and universes are fixes.
    That is, when the user writes \c n inside the section she is really getting the term returned by this function.
*/
expr mk_section_local_ref(name const & n, levels const & sec_ls, unsigned num_sec_params, expr const * sec_params);
inline expr mk_section_local_ref(name const & n, levels const & sec_ls, buffer<expr> const & sec_params) {
    return mk_section_local_ref(n, sec_ls, sec_params.size(), sec_params.data());
}
/** \brief Return true iff \c e is a term of the form
    <tt>(@^-1 (@n.{ls} @l_1 ... @l_n))</tt> where
    \c n is a constant and l_i's are local constants.

    \remark is_section_local_ref(mk_section_local_ref(n, ls, num_ps, ps)) always hold.
*/
bool is_section_local_ref(expr const & e);
/** \brief Given a term \c e s.t. is_section_local_ref(e) is true, remove all local constants in \c to_remove.
    That is, if \c e is of the form
    <tt>(@^-1 (@n.{u_1 ... u_k} @l_1 ... @l_n))</tt>
    Then, return a term s.t.
       1) any l_i s.t. mlocal_name(l_i) in \c locals_to_remove is removed.
       2) any level u_j in \c lvls_to_remove is removed
*/
expr update_section_local_ref(expr const & e, name_set const & lvls_to_remove, name_set const & locals_to_remove);

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

/** \brief Instantiate metavariable application \c meta (?M ...) using \c subst  */
expr instantiate_meta(expr const & meta, substitution & subst);

/** \brief Return a 'failed to synthesize placholder' justification for the given
    metavariable application \c m of the form (?m l_1 ... l_k) */
justification mk_failed_to_synthesize_jst(environment const & env, expr const & m);

/** \brief Return a justification for \c v_type being definitionally equal to \c t,
    <tt> v : v_type</tt>, the expressiong \c src is used to extract position information.
*/
justification mk_type_mismatch_jst(expr const & v, expr const & v_type, expr const & t, expr const & src);
inline justification mk_type_mismatch_jst(expr const & v, expr const & v_type, expr const & t) {
    return mk_type_mismatch_jst(v, v_type, t, v);
}

/** \brief Given a metavariable application (?m l_1 ... l_n), apply \c s to the types of
    ?m and local constants l_i
    Return the updated expression and a justification for all substitutions.
*/
pair<expr, justification> update_meta(expr const & meta, substitution s);
}
