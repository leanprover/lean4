/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/** \brief Return the eta expanded normal form for \c e.
    \pre \c e does not contain variables nor metavariables. */
expr eta_expand(environment const & env, expr const & e);
}
