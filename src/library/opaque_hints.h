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
/** \brief Return true iff \c n was exposed using \c expose_definition */
bool is_exposed(environment const & env, name const & n);
/** \brief Create a type checker that uses a converter based on the opaque/transparent hints
    provided by the user.

    If \c relax_main_opaque is true, then all opaque definitions from the main module
    are treated as transparent.

    If \c only_main_transparent is true, then only transparent definitions from the main module
    are treated as transparent.

    The hints provided using #hide_definition and #expose_definition override this behavior.
*/
std::unique_ptr<type_checker> mk_type_checker_with_hints(environment const & env,
                                                         name_generator const & ngen,
                                                         bool relax_main_opaque,
                                                         bool only_main_transparent = false);
}
