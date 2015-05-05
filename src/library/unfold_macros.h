/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Unfold any macro occurring in \c e that has trust level higher than the one
    allowed in \c env.

    \remark We use this function before sending declarations to the kernel.
    The kernel refuses any expression containing "untrusted" macros, i.e.,
    macros with trust level higher than the one allowed.
*/
expr unfold_untrusted_macros(environment const & env, expr const & e);

declaration unfold_untrusted_macros(environment const & env, declaration const & d);

expr unfold_all_macros(environment const & env, expr const & e);

declaration unfold_all_macros(environment const & env, declaration const & d);
}
