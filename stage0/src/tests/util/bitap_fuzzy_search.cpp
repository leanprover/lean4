/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/bitap_fuzzy_search.h"
using namespace lean;

static void tst1() {
    bitap_fuzzy_search matcher("dicr", 1);
    lean_assert(matcher.match("discriminate"));
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}
