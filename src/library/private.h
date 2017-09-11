/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/optional.h"
#include "kernel/environment.h"

namespace lean {
/**
   \brief This is an auxiliary function used to simulate private declarations. Whenever we want to create a "private"
   declaration, this module creates an internal "hidden" name that is not accessible to users.
   In principle, users can access the internal names if they want by applying themselves the procedure used to create
   the "hidden" names.

   The optional \c base_hash can be used to influence the "hidden" name associated with \c n.

   The mapping between \c n and the "hidden" name is saved  in the .olean files.
*/
pair<environment, name> add_private_name(environment const & env, name const & n, optional<unsigned> const & base_hash);

/**
    \brief Return the user name associated with the hidden name \c n.

    \remark The "user name" is the argument provided to \c add_private_name, and "hidden name" is the name returned
    by \c add_private_name.
*/
optional<name> hidden_to_user_name(environment const & env, name const & n);

bool is_private(environment const & env, name const & n);

pair<environment, name> mk_private_prefix(environment const & env, name const & n, optional<unsigned> const & base_hash);

/* Create a private name based on \c c and get_pos_info_provider(), and register it using \c add_private_name */
pair<environment, name> mk_private_name(environment const & env, name const & c);

/* Create a private prefix that is going to be use to generate many private names.
   This function registers the private prefix in the environment. */
pair<environment, name> mk_private_prefix(environment const & env, optional<unsigned> const & extra_hash);

/* Similar to the previous function, but generate an extra_hash using get_pos_info_provider */
pair<environment, name> mk_private_prefix(environment const & env);

/* Register a \c n as the name for private name \c prv_n. \c prv_n must have been constructed using
   a prefix returned by \c mk_private_prefix. */
environment register_private_name(environment const & env, name const & n, name const & prv_n);

/* Return true iff a prefix of `n` is registered as a private prefix in the given environment. */
bool has_private_prefix(environment const & env, name const & n);

/* Return some name iff a prefix of `n` is registered as a private prefix in the given environment. */
optional<name> get_private_prefix(environment const & env, name const & n);

void initialize_private();
void finalize_private();
}
