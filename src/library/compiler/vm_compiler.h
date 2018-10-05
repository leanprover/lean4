/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
environment vm_compile(environment const & env, options const & opts, constant_info const & d);
/* Similar to previous function. It is used to compile meta mutually recursive definitions. */
environment vm_compile(environment const & env, options const & opts, buffer<constant_info> const & ds);

void initialize_vm_compiler();
void finalize_vm_compiler();
}
