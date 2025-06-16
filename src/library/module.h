/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich
*/
#pragma once
#include <string>
#include <iostream>
#include <utility>
#include <vector>
#include "runtime/optional.h"
#include "library/elab_environment.h"

namespace lean {
/** \brief Store module using \c env. */
LEAN_EXPORT void write_module(elab_environment const & env, std::string const & olean_fn);
}
