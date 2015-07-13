/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "kernel/type_checker.h"
#include "library/util.h"
#include "library/tactic/util.h"
#include "frontends/lean/local_decls.h"

namespace lean {
class parser;
/** \brief Consume tokes until 'end' token is consumed */
void consume_until_end(parser & p);

/** \brief Parse optional '[persistent]' modifier.
    return true if it is was found, and paremeter \c persistent to true.
*/
bool parse_persistent(parser & p, bool & persistent);

/** \brief Throw and error if the current token is not a command, nor a '.', nor an end-of-file. */
void check_command_period_or_eof(parser const & p);
/** \brief Throw and error if the current token is not a command, nor an open binder, nor a '.', nor an end-of-file. */
void check_command_period_open_binder_or_eof(parser const & p);
void check_atomic(name const & n);
void check_in_section(parser const & p);
bool is_root_namespace(name const & n);
name remove_root_prefix(name const & n);
/** \brief Return the local levels in \c ls that are not tagged as variables.
    A local level is tagged as variable if it associated with a variable.
*/
levels collect_local_nonvar_levels(parser & p, level_param_names const & ls);
/** \brief Collect local constants occurring in \c type and \c value, sort them, and store in ctx_ps */
void collect_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & ctx_ps);
name_set collect_univ_params_ignoring_tactics(expr const & e, name_set const & ls = name_set());
/** \brief Copy the local names to \c ps, then sort \c ps (using the order in which they were declared). */
void sort_locals(buffer<expr> const & locals, parser const & p, buffer<expr> & ps);
/** \brief Remove from \c ps local constants that are tagged as variables. */
void remove_local_vars(parser const & p, buffer<expr> & ps);
/** \brief Remove from \c ls any universe level that is tagged as variable in \c p */
levels remove_local_vars(parser const & p, levels const & ls);
list<expr> locals_to_context(expr const & e, parser const & p);
/** \brief Create the term <tt>(as_atomic (@n.{ls} @params[0] ... @params[num_params-1]))</tt>
    When we declare \c n inside of a context, the parameters and universes are fixed.
    That is, when the user writes \c n inside the section she is really getting the term returned by this function.
*/
expr mk_local_ref(name const & n, levels const & ctx_ls, unsigned num_ctx_params, expr const * ctx_params);
inline expr mk_local_ref(name const & n, levels const & ctx_ls, buffer<expr> const & ctx_params) {
    return mk_local_ref(n, ctx_ls, ctx_params.size(), ctx_params.data());
}
/** \brief Return true iff \c e is a term of the form
    <tt>(as_atomic (@n.{ls} @l_1 ... @l_n))</tt> where
    \c n is a constant and l_i's are local constants.

    \remark is_local_ref(mk_local_ref(n, ls, num_ps, ps)) always hold.
*/
bool is_local_ref(expr const & e);
/** \brief Given a term \c e s.t. is_local_ref(e) is true, remove all local constants in \c to_remove.
    That is, if \c e is of the form
    <tt>(as_atomic (@n.{u_1 ... u_k} @l_1 ... @l_n))</tt>
    Then, return a term s.t.
       1) any l_i s.t. mlocal_name(l_i) in \c locals_to_remove is removed.
       2) any level u_j in \c lvls_to_remove is removed
*/
expr update_local_ref(expr const & e, name_set const & lvls_to_remove, name_set const & locals_to_remove);

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

/** \brief Auxiliary function for check/eval/find_decl */
std::tuple<expr, level_param_names> parse_local_expr(parser & p, bool relaxed = true);

optional<name> is_uniquely_aliased(environment const & env, name const & n);

/** \brief Get declaration 'short-name' that can uniquely identify it. */
name get_decl_short_name(name const & d, environment const & env);

/** \brief Open 'num' notation and aliases. */
environment open_num_notation(environment const & env);
/** \brief Open 'std.prec' aliases */
environment open_prec_aliases(environment const & env);
/** \brief Open 'std.priority' aliases */
environment open_priority_aliases(environment const & env);
name get_priority_namespace();

char const * open_binder_string(binder_info const & bi, bool unicode);
char const * close_binder_string(binder_info const & bi, bool unicode);

/** \brief Cleanup expression after elaboration. */
expr postprocess(environment const & env, expr const & e);

/** \brief Parse `[priority <num>]`. Return none if current token is not `[priority` */
optional<unsigned> parse_priority(parser & p);

/** \brief Parse option name */
pair<name, option_kind> parse_option_name(parser & p, char const * error_msg);
}
