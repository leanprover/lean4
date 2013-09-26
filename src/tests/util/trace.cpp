/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/trace.h"
using namespace lean;

int main() {
    lean_assert(!is_trace_enabled("name"));
    enable_trace("name");
    lean_assert(is_trace_enabled("name"));
    disable_trace("name");
    lean_assert(!is_trace_enabled("name"));
    return has_violations() ? 1 : 0;
}
