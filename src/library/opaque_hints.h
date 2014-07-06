/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/*
   Opaque hints are used to 'help/guide' the elaborator and unifier.
   We can use them to mark additional definitions as opaque.
   Note that we are not changing the status of the definitions, we are
   only changing how the elaborator/unifier treats them.

   These hints are not used when we type check a definition before
   adding it to the kernel.
*/

/** \brief Mark the definition named \c n as opaque for the elaborator/unifier. */
environment hide_definition(environment const & env, name const & n);
/** \brief Undo the modification made with \c hide_definition. */
environment expose_definition(environment const & env, name const & n);
/**
    \brief By default, the elaborator/unifier will treat the opaque
    definitions of the current/main module as transparent. We can
    change this behavior using this function.
*/
environment set_main_module_opaque_defs(environment const & env, bool f);
/** \brief Create a type checker that takes the hints into account. */
std::unique_ptr<type_checker> mk_type_checker_with_hints(environment const & env, name_generator const & ngen);
}
