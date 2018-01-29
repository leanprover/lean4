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
#include "library/locals.h"
#include "library/vm/vm.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/local_level_decls.h"

namespace lean {
class parser;
/** \brief Consume tokens until 'end' token is consumed or a command/eof is found */
void consume_until_end_or_command(parser & p);

/** \brief Throw and error if the current token is not a command, nor a '.', nor an end-of-file. */
void check_command_period_docstring_or_eof(parser const & p);
/** \brief Throw and error if the current token is not a command, nor an open binder, nor a '.', nor an end-of-file. */
void check_command_period_open_binder_or_eof(parser const & p);
void check_atomic(name const & n);
void check_in_section(parser const & p);
bool is_root_namespace(name const & n);
name remove_root_prefix(name const & n);

/** \brief Return true iff the next token is the prefix of a pattern-matching equation */
bool is_eqn_prefix(parser & p, bool bar_only = false);

/** \brief Return the local levels in \c ls that are not tagged as variables.
    A local level is tagged as variable if it associated with a variable.
*/
levels collect_local_nonvar_levels(parser & p, level_param_names const & ls);
/** \brief Collect local constants occurring in \c type and \c value, sort them, and store in ctx_ps */
void collect_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & ctx_ps);
void collect_annonymous_inst_implicit(parser const & p, collected_locals & ls);
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
expr Fun(expr const & local, expr const & e, parser & p);
/** \brief Pi(locals, e), but also propagate \c e position to result */
expr Pi(buffer<expr> const & locals, expr const & e, parser & p);
expr Pi(expr const & local, expr const & e, parser & p);
/** \brief Similar to Pi(locals, e, p), but the types are marked as 'as-is' (i.e., they are not processed by the elaborator. */
expr Pi_as_is(buffer<expr> const & locals, expr const & e, parser & p);
expr Pi_as_is(expr const & local, expr const & e);
/** \brief Create the resultant universe level using the levels computed during introduction rule elaboration */
level mk_result_level(buffer<level> const & r_lvls);

/** \brief Auxiliary function for check/eval/find_decl */
std::tuple<expr, level_param_names> parse_local_expr(parser & p, name const & decl_name, bool relaxed = true);

optional<name> is_uniquely_aliased(environment const & env, name const & n);

/** \brief Get declaration 'short-name' that can uniquely identify it. */
name get_decl_short_name(name const & d, environment const & env);

/** \brief Open 'std.prec' aliases */
environment open_prec_aliases(environment const & env);
/** \brief Open 'std.priority' aliases */
environment open_priority_aliases(environment const & env);
name get_priority_namespace();

char const * open_binder_string(binder_info const & bi, bool unicode);
char const * close_binder_string(binder_info const & bi, bool unicode);

/** \brief Parse option name */
pair<name, option_kind> parse_option_name(parser & p, char const * error_msg);

expr quote(unsigned u);
expr quote(char const * str);
expr quote(name const & n);

expr mk_no_info(expr const & e);
bool is_no_info(expr const & e);

expr mk_opt_param(expr const & t, expr const & val);
expr mk_auto_param(expr const & t, name const & tac_name);
expr parse_auto_param(parser & p, expr const & type);

/* Add frozen annotation around constants and local constants occurring in \c e.
   This annotation is used to prevent lean from resolving the names again
   at tactic execution time. See resolve_names_fn at elaborator.cpp.

   In notation declarations, names are resolved at notation declaration time.
   Users do not expect them to be resolved again at tactic execution time.
   See issue #1468. */
expr freeze_names(expr const & e);
/* Return true iff \c e is marked with a frozen_name annotation. */
bool is_frozen_name(expr const & e);

/* Field notation support */
expr mk_field_notation(expr const & e, name const & field);
expr mk_field_notation_compact(expr const & e, char const * field);
expr mk_field_notation(expr const & e, unsigned fidx);
bool is_field_notation(expr const & e);
bool is_anonymous_field_notation(expr const & e);
name const & get_field_notation_field_name(expr const & e);
unsigned get_field_notation_field_idx(expr const & e);

environment compile_expr(environment const & env, name const & n, level_param_names const & ls, expr const & type, expr const & e, pos_info const & pos);
vm_obj eval_closed_expr(environment const & env, name const & n, expr const & type, expr const & e, pos_info const & pos);

expr mk_lean_list(parser & p, buffer<expr> const & es, pos_info const & pos);
expr mk_lean_list(buffer<expr> const & es);

void initialize_frontend_lean_util();
void finalize_frontend_lean_util();
}
