/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "options.h"
#include "test.h"
using namespace lean;

static void tst1() {
    options opt;
    std::cout << opt << "\n";
    opt = opt.update("tst", 10);
    std::cout << opt << "\n";
    opt = opt.update("foo", true);
    std::cout << opt << "\n";
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}
