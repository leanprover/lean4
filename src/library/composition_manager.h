/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/type_checker.h"

namespace lean {
/** \brief Define the composition of g and f, if the environment already contains one created using \c compose, returns it.
    Otherwise, this procedure defines one and uses name \c gf. If \c gf is none, then use g+f as the name.
    If the environment already has a definition with this name, then adds the prefix _idx, where idx is a numeral.
    The result is a pair (new environment, new constant name).
*/
pair<environment, name> compose(environment const & env, type_checker & tc, name const & g, name const & f, optional<name> const & gf = optional<name>());
pair<environment, name> compose(environment const & env, name const & g, name const & f, optional<name> const & gf = optional<name>());
void initialize_composition_manager();
void finalize_composition_manager();
}
