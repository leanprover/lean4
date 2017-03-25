/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
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
