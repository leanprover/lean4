/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
environment vm_compile(environment const & env, declaration const & d, bool optimize_bytecode = true);
/* Similar to previous function. It is used to compile meta mutually recursive definitions. */
environment vm_compile(environment const & env, buffer<declaration> const & ds, bool optimize_bytecode = true);

void initialize_vm_compiler();
void finalize_vm_compiler();
}
