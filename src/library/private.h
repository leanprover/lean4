/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/optional.h"
#include "util/lua.h"
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
std::pair<environment, name> add_private_name(environment const & env, name const & n, optional<unsigned> const & base_hash);

/**
    \brief Return the user name associated with the hidden name \c n.

    \remark The "user name" is the argument provided to \c add_private_name, and "hidden name" is the name returned
    by \c add_private_name.
*/
optional<name> hidden_to_user_name(environment const & env, name const & n);

/**
    \brief Return the hidden name associated with the user name \c n.

    \remark The "user name" is the argument provided to \c add_private_name, and "hidden name" is the name returned
    by \c add_private_name.

    \remark The mapping user -> hidden name is *not* stored in .olean files.
    In this way, users don't have "access" to the names.

    \see add_private_name
*/
optional<name> user_to_hidden_name(environment const & env, name const & n);

void open_private(lua_State * L);
}
