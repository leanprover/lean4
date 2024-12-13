/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "library/elab_environment.h"
#include "runtime/object.h"

namespace lean {
namespace ir {
/** \brief Run `n` using the "boxed" ABI, i.e. with all-owned parameters. */
object * run_boxed(elab_environment const & env, options const & opts, name const & fn, unsigned n, object **args);
LEAN_EXPORT uint32 run_main(elab_environment const & env, options const & opts, int argv, char * argc[]);
}
void initialize_ir_interpreter();
void finalize_ir_interpreter();
}
