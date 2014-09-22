/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/serializer.h"
#include "util/name.h"

namespace lean {
void initialize_util_module() {
    initialize_serializer();
    initialize_name();
}
void finalize_util_module() {
    finalize_name();
    finalize_serializer();
}
}
