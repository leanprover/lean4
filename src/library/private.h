/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "runtime/optional.h"
#include "kernel/environment.h"

namespace lean {
/**
   \brief This is an auxiliary function used to simulate private declarations.
*/
pair<environment, name> add_private_name(environment const & env, name const & n);

/**
    \brief Return the user name associated with the hidden name \c n.

    \remark The "user name" is the argument provided to \c add_private_name, and "hidden name" is the name returned
    by \c add_private_name.
*/
optional<name> hidden_to_user_name(environment const & env, name const & n);

bool is_private(environment const & env, name const & n);

/* Create a private prefix that is going to be use to generate many private names.
   This function registers the private prefix in the environment. */
pair<environment, name> mk_private_prefix(environment const & env);
pair<environment, name> mk_private_prefix(environment const & env, name const & n);

/* Create a private name based on \c c and get_pos_info_provider(), and register it using \c add_private_name */
pair<environment, name> mk_private_name(environment const & env, name const & c);

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
