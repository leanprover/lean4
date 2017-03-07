/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
namespace lean {
void initialize_parray() {
    register_trace_class(name{"array", "update"});
}
void finalize_parray() {
}
}
