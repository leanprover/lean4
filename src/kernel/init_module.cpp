/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
namespace lean {
void initialize_kernel_module() {
    initialize_environment();
}
void finalize_kernel_module() {
    finalize_environment();
}
}
