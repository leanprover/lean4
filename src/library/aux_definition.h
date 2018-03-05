/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
/** Helper class for creating closures for nested terms.

    There are two phases:
    1- Parameter and metavariable collection.
    2- Closure creation.

    The methods \c collect are used in the first phase.
    The method \c finalize_collection moves object to the second phase.

    The collection phase collects parameters and metavariables.
    A new parameter is created for each metavariable found in a subterm.

    Parameter and metavariables occurring in the types of collected
    parameters and metavariables are also collected.

    The method \c finalize_collection moves the state to phase 2.
    It also creates a new (normalized) parameter for each collected parameter and metavariable.
    The type of the new parameter is the type of the source after normalization.
    All new parameters are sorted based on dependencies.
*/
class closure_helper {
    type_context_old &  m_ctx;
    name            m_prefix;
    unsigned        m_next_idx;
    name_set        m_found_univ_params;
    name_map<level> m_univ_meta_to_param;
    name_map<level> m_univ_meta_to_param_inv;
    name_set        m_found_local;
    name_map<expr>  m_meta_to_param;
    name_map<expr>  m_meta_to_param_inv;
    buffer<name>    m_level_params;
    buffer<expr>    m_params;
    bool            m_finalized_collection{false};
    buffer<expr>    m_norm_params;

public:
    closure_helper(type_context_old & ctx):
        m_ctx(ctx),
        m_prefix("_aux_param"),
        m_next_idx(0) {}

    type_context_old & ctx() { return m_ctx; }

    /* \pre finalize_collection has not been invoked */
    level collect(level const & l);
    /* \pre finalize_collection has not been invoked */
    levels collect(levels const & ls);
    /* \pre finalize_collection has not been invoked */
    expr collect(expr const & e);

    /* \pre finalize_collection has not been invoked */
    void finalize_collection();

    /* Replace parameters in \c e with corresponding normalized parameters, obtain e', and
       then return (Pi N, e') where N are the normalized parameters.

       Remark \c e must not contain meta-variables. We can ensure this constraint by using the
       collect method

       \pre finalize_collection has been invoked */
    expr mk_pi_closure(expr const & e);

    /* Replace parameters in \c e with corresponding normalized parameters, obtain e', and
       then return (fun N, e') where N are the normalized parameters.

       Remark \c e must not contain meta-variables. We can ensure this constraint by using the
       collect method

       \pre finalize_collection has been invoked */
    expr mk_lambda_closure(expr const & e);

    /* Return the level parameters and meta-variables collected by collect methods.

      \pre finalize_collection has been invoked */
    void get_level_closure(buffer<level> & ls);
    /* Return the parameters and meta-variables collected by collect methods.

      \pre finalize_collection has been invoked */
    void get_expr_closure(buffer<expr> & ps);

    /* Return the normalized paramaters created by this helper object.

       \pre finalize_collection has been invoked */
    buffer<expr> const & get_norm_closure_params() const;

    /* Return the name of normalized parameters. That is, it includes the collected
       level parameters and new parameters created for universe meta-variables.

       \pre finalize_collection has been invoked */
    list<name> get_norm_level_names() const { return to_list(m_level_params); }
};

/** \brief Create an auxiliary definition with name `c` where `type` and `value` may contain local constants and
    meta-variables. This function collects all dependencies (universe parameters, universe metavariables,
    local constants and metavariables). The result is the updated environment and an expression of the form

          (c.{l_1 ... l_n} a_1 ... a_m)

    where l_i's and a_j's are the collected dependencies.

    If is_meta is none, then function also computes whether the new definition should be tagged as trusted or not.

    The updated environment is an extension of ctx.env() */
pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & type, expr const & value,
                                          optional<bool> const & is_meta = optional<bool>());
/** \brief Similar to mk_aux_definition, but the type of value is inferred using ctx. */
pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & value,
                                          optional<bool> const & is_meta = optional<bool>());
/** \brief Similar to mk_aux_definition, but creates a lemma */
pair<environment, expr> mk_aux_lemma(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                     name const & c, expr const & type, expr const & value);

pair<environment, expr> abstract_nested_proofs(environment const & env, metavar_context const & mctx, local_context const & lctx, name const & base_name, expr const & e);
pair<environment, expr> abstract_nested_proofs(environment const & env, name const & base_name, expr const & e);
}
