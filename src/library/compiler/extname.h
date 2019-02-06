/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
optional<name> get_extname_for(environment const & env, name const & n);
inline bool has_extname(environment const & env, name const & n) { return static_cast<bool>(get_extname_for(env, n)); }
void initialize_extname();
void finalize_extname();
}
