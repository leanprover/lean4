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
/* Create a private prefix that is going to be use to generate many private names.
   This function registers the private prefix in the environment. */
pair<environment, name> mk_private_prefix(environment const & env);
pair<environment, name> mk_private_name(environment const & env, name const & n);
optional<name> private_to_user_name(name const & n);
bool is_private(name const & n);
optional<name> get_private_prefix(name const & n);

void initialize_private();
void finalize_private();
}
