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

static void tst2() {
    options opt;
    opt = update(opt, name{"test", "foo"}, 10);
    opt = update(opt, name{"color"}, 20);
    opt = update(opt, name{"ratio"}, 10.5);
    sexpr s{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    opt = update(opt, name{"sp", "order"}, sexpr{s, s, s, s, s, s});
    opt = update(opt, name{"test", "long", "names", "with", "several", "parts"}, true);
    std::cout << pp(opt) << "\n";
}

int main() {
    continue_on_violation(true);
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}
